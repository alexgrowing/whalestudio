import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosedStatement
import GroundTheory.AutomorphicForms.IwahoriFactorization
import GroundTheory.AutomorphicForms.GeometricLemmaCellSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open GroundTheory.Automorphic.GLnLocal
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.Rodier.OpenBump

theorem exists_smInd_bump {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (H K : Subgroup G) (hK : IsOpen (K : Set G))
    (σ : Representation ℂ H W) (v : W) (hv : ∀ c : H, (c : G) ∈ K → σ c v = v) :
    ∃ f : smoothPart (ind H σ), (∀ g, f.1.1 g ≠ 0 → ∃ p ∈ H, ∃ κ ∈ K, g = p * κ) ∧
      ∀ κ ∈ K, f.1.1 κ = v := by
  classical
  have key : ∀ p q : H, (p : G)⁻¹ * q ∈ K → σ q v = σ p v := by
    intro p q hpq
    have h1 : σ (p⁻¹ * q) v = v := hv _ (by simpa using hpq)
    have h2 : q = p * (p⁻¹ * q) := by group
    calc σ q v = σ (p * (p⁻¹ * q)) v := by rw [← h2]
      _ = σ p (σ (p⁻¹ * q) v) := by rw [map_mul]; rfl
      _ = σ p v := by rw [h1]
  let S : G → Prop := fun x => ∃ p : H, (p : G)⁻¹ * x ∈ K
  let pick : G → H := fun x => if h : S x then h.choose else 1
  have pick_spec : ∀ x, S x → ((pick x : H) : G)⁻¹ * x ∈ K := by
    intro x h
    simp only [pick, dif_pos h]
    exact h.choose_spec
  let F : G → W := fun x => if S x then σ (pick x) v else 0
  have F_pos : ∀ x, S x → F x = σ (pick x) v := fun x h => if_pos h
  have F_neg : ∀ x, ¬ S x → F x = 0 := fun x h => if_neg h
  have S_left : ∀ (q : H) x, S x → S (q * x) := by
    rintro q x ⟨p, hp⟩
    exact ⟨q * p, by simpa [mul_assoc] using hp⟩
  have S_right : ∀ c ∈ K, ∀ x, S x → S (x * c) := by
    rintro c hc x ⟨p, hp⟩
    exact ⟨p, by simpa [mul_assoc] using K.mul_mem hp hc⟩
  have hlaw : F ∈ indSpace H σ := by
    intro q x
    by_cases hx : S x
    · have hqx := S_left q x hx
      rw [F_pos _ hqx, F_pos _ hx, ← Module.End.mul_apply, ← map_mul]
      refine key _ _ ?_
      have h3 := K.mul_mem (pick_spec x hx) (K.inv_mem (pick_spec _ hqx))
      convert h3 using 1
      simp only [Subgroup.coe_mul]
      group
    · have hqx : ¬ S (q * x) := fun h => hx (by
        have := S_left q⁻¹ _ h
        simpa using this)
      rw [F_neg _ hqx, F_neg _ hx, map_zero]
  have hfix : ∀ c ∈ K, ∀ x, F (x * c) = F x := by
    intro c hc x
    by_cases hx : S x
    · have hxc := S_right c hc x hx
      rw [F_pos _ hxc, F_pos _ hx]
      refine key _ _ ?_
      have h3 := K.mul_mem (K.mul_mem (pick_spec x hx) hc) (K.inv_mem (pick_spec _ hxc))
      convert h3 using 1
      group
    · have hxc : ¬ S (x * c) := fun h => hx (by
        have := S_right c⁻¹ (K.inv_mem hc) _ h
        simpa using this)
      rw [F_neg _ hxc, F_neg _ hx]
  have hfix' : ∀ c ∈ K, ind H σ c ⟨F, hlaw⟩ = ⟨F, hlaw⟩ :=
    fun c hc => Subtype.ext (funext fun x => hfix c hc x)
  have hsm : (⟨F, hlaw⟩ : indSpace H σ) ∈ smoothPart (ind H σ) :=
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem) fun c hc => hfix' c hc)
  refine ⟨⟨⟨F, hlaw⟩, hsm⟩, fun g hg => ?_, fun κ hκ => ?_⟩
  · have hS : S g := by
      by_contra hS
      exact hg (F_neg g hS)
    exact ⟨pick g, (pick g).2, _, pick_spec g hS, by group⟩
  · have hS : S κ := ⟨1, by simpa using hκ⟩
    show F κ = v
    rw [F_pos κ hS]
    refine hv _ ?_
    have h3 := K.mul_mem hκ (K.inv_mem (pick_spec κ hS))
    simpa using h3

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_one_of_mem_parab_of_mem_lower {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) {x : GL n k} (h1 : x ∈ parab k e) (h2 : x ∈ unipRadLower k e) : x = 1 := by
  obtain ⟨h3, h4⟩ := (mem_unipRadLower k).1 h2
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  have hne : ∀ c : α, ∀ (i' : m c) (b' : α) (j' : m b'), c ≠ b' →
      (1 : Matrix n n k) (e ⟨c, i'⟩) (e ⟨b', j'⟩) = 0 := by
    intro c i' b' j' hcb
    refine Matrix.one_apply_ne fun h' => hcb ?_
    have := e.injective h'
    exact congrArg Sigma.fst this
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [(mem_parabLower_iff k).1 h3 a b i j hab, Units.val_one, hne a i b j hab.ne]
  · rw [h4 a i j, Units.val_one]
    by_cases e' : i = j
    · subst e'; simp
    · rw [Matrix.one_apply_ne e', Matrix.one_apply_ne]
      intro h'
      exact e' (by simpa using e.injective h')
  · rw [mem_parab_iff.1 h1 a b i j hab, Units.val_one, hne a i b j hab.ne']

theorem exists_parab_mul_lower {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {m : ℕ} (hm : 1 ≤ m)
    {κ : GL (Fin N) k} (hκ : κ ∈ congruenceSubgroup k N m) :
    ∃ q ∈ parab k (stdBlocks d hd), ∃ z ∈ congruenceSubgroup k N m,
      z ∈ unipRadLower k (stdBlocks d hd) ∧ κ = q * z := by
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization' (blk (stdBlocks d hd)) hm κ hκ
  have up : ∀ g ∈ GroundTheory.Automorphic.Iwasawa.blockUpper k N (blk (stdBlocks d hd)), g ∈ parab k (stdBlocks d hd) :=
    fun g hg => (GroundTheory.Automorphic.Iwasawa.mem_blockUpper k N).1 hg
  refine ⟨x * y, (parab k _).mul_mem (up _ (GroundTheory.Automorphic.Parabolic.unipotentRadical_le_blockUpper hx.2))
    (up _ (GroundTheory.Automorphic.Parabolic.levi_le_blockUpper hy.2)), z, hz.1, ?_, rfl⟩
  obtain ⟨h1, h2⟩ := GroundTheory.Automorphic.Parabolic.mem_unipotentRadical.1 hz.2
  have h1' := (GroundTheory.Automorphic.Iwasawa.mem_blockUpper k N).1 h1
  refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j hab => h1' ?_, fun a i j => ?_⟩
  · simpa [blk] using hab
  · rw [h2 _ _ (by simp [blk])]
    by_cases e' : i = j
    · subst e'; simp
    · rw [Matrix.one_apply_ne e', Matrix.one_apply_ne]
      intro h'
      exact e' (by simpa using (stdBlocks d hd).injective h')

theorem exists_level (ψ : AddChar k Circle) (hψ : Continuous ψ) {h N : ℕ} (d : Fin h → ℕ)
    (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (hρ : IsSmooth ρ) (v : W) :
    ∃ m, 1 ≤ m ∧ (∀ c : parab k (stdBlocks d hd), (c : GL (Fin N) k) ∈ congruenceSubgroup k N m →
        ((twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdBlocks d hd))) c v = v) ∧
      ∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ congruenceSubgroup k N m →
        whitChar ψ N ⟨l, hl⟩ = 1 := by
  have hs := isSmooth_twist hρ (isSmoothChar_deltaHalf k (m := fun a => Fin (d a))) v
  have hpre := hs.preimage (ProdIrr.continuous_leviProj (stdBlocks d hd))
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hpre
  have hw : IsOpen ((whitChar ψ N).ker : Set (unipB k (Fin N))) :=
    GlobalTheory.Whittaker.isSmoothChar_whitChar hψ
  obtain ⟨U₂, hU₂, hUe₂⟩ := isOpen_induced_iff.1 hw
  have h1 : (1 : GL (Fin N) k) ∈ U := by
    have h2 : (1 : parab k (stdBlocks d hd)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      simp
    exact h2
  have h1₂ : (1 : GL (Fin N) k) ∈ U₂ := by
    have h2 : (1 : unipB k (Fin N)) ∈ Subtype.val ⁻¹' U₂ := by
      rw [hUe₂]
      exact one_mem _
    exact h2
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one k N).mem_iff.1 ((hU.inter hU₂).mem_nhds ⟨h1, h1₂⟩)
  refine ⟨m + 1, by omega, fun c hc => ?_, fun l hl hlK => ?_⟩
  · have h2 : c ∈ Subtype.val ⁻¹' U := (hm (congruenceSubgroup_antitone k N (Nat.le_succ m) hc)).1
    rw [hUe] at h2
    exact h2
  · have h2 : (⟨l, hl⟩ : unipB k (Fin N)) ∈ Subtype.val ⁻¹' U₂ :=
      (hm (congruenceSubgroup_antitone k N (Nat.le_succ m) hlK)).2
    rw [hUe₂] at h2
    exact h2

theorem exists_openFns_bump : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∀ v : W, ∃ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd ∧ IsCompact (L₀ : Set (GL (Fin N) k)) ∧ (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) ∧ (∀ (l : GL (Fin N) k) (hl : l ∈ unipB k (Fin N)), l ∈ L₀ → whitChar ψ N ⟨l, hl⟩ = 1) ∧ ∃ f ∈ openFns d hd ρ, (∀ u ∈ L₀, f.1.1 (pm k (wOpen d hd) * u) = v) ∧ ∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1 (pm k (wOpen d hd) * u) = 0 := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ v
  obtain ⟨m, hm1, hσ, hW⟩ := exists_level ψ hψ d hd ρ hρ v
  obtain ⟨hI1, -, hI3⟩ := GlobalTheory.T.open_cell_unipotent_uniqueness_closed k h N d hd
  have hKo := isOpen_congruenceSubgroup k N m
  have hKc := isCompact_congruenceSubgroup k N m
  set K := congruenceSubgroup k N m with hKdef
  set w := pm k (wOpen d hd) with hwdef
  have hwI : w ∈ integralGL k N := GroundTheory.Automorphic.Parabolic.permGL_mem_integralGL _
  have hconj : ∀ x ∈ K, w * x * w⁻¹ ∈ K := fun x hx => conj_mem_congruenceSubgroup k N hwI hx
  have hconj' : ∀ x ∈ K, w⁻¹ * x * w ∈ K := fun x hx => by
    simpa using conj_mem_congruenceSubgroup k N ((integralGL k N).inv_mem hwI) hx
  obtain ⟨f₀, hsup, hval⟩ := exists_smInd_bump (parab k (stdBlocks d hd)) K hKo
    ((twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdBlocks d hd))) v hσ
  let f : IndSp (stdBlocks d hd) ρ := smInd (parab k (stdBlocks d hd))
    ((twist ρ (deltaHalf k fun a => Fin (d a))).comp (leviProj k (stdBlocks d hd))) w⁻¹ f₀
  have hf : ∀ g, f.1.1 g = f₀.1.1 (g * w⁻¹) := fun _ => rfl
  let L₀ : Subgroup (GL (Fin N) k) := unipU k d hd ⊓ K.comap (MulAut.conj w).toMonoidHom
  have memL : ∀ u, u ∈ L₀ ↔ u ∈ unipU k d hd ∧ w * u * w⁻¹ ∈ K := fun u => Iff.rfl
  have memU : ∀ u ∈ unipU k d hd, w * u * w⁻¹ ∈ unipRadLower k (stdBlocks d hd) :=
    fun u hu => hu.2
  have hcont : Continuous fun g : GL (Fin N) k => w⁻¹ * g * w := by fun_prop
  have hcont' : Continuous fun g : GL (Fin N) k => w * g * w⁻¹ := by fun_prop
  refine ⟨L₀, inf_le_left, ?_, ⟨(fun g => w * g * w⁻¹) ⁻¹' (K : Set _), hKo.preimage hcont', ?_⟩,
    ?_, f, ?_, ?_, ?_⟩
  · have hset : (L₀ : Set (GL (Fin N) k)) =
        ((fun g => w⁻¹ * g * w) '' (K : Set (GL (Fin N) k))) ∩ (unipU k d hd : Set _) := by
      ext u
      constructor
      · intro hu
        exact ⟨⟨_, ((memL u).1 hu).2, by group⟩, ((memL u).1 hu).1⟩
      · rintro ⟨⟨x, hx, rfl⟩, hu⟩
        refine (memL _).2 ⟨hu, ?_⟩
        have : w * (w⁻¹ * x * w) * w⁻¹ = x := by group
        rw [this]
        exact hx
    rw [hset]
    exact (hKc.image hcont).inter_right hI3
  · ext u
    exact ⟨fun hu => (memL u).2 ⟨hu.2, hu.1⟩, fun hu => ⟨((memL u).1 hu).2, ((memL u).1 hu).1⟩⟩
  · intro l hl hlL
    refine hW l hl ?_
    have := hconj' _ ((memL l).1 hlL).2
    have e : w⁻¹ * (w * l * w⁻¹) * w = l := by group
    rwa [e] at this
  · intro g hg
    rw [hf] at hg
    obtain ⟨p, hp, κ, hκ, e⟩ := hsup _ hg
    obtain ⟨q, hq, z, hz, hzl, rfl⟩ := exists_parab_mul_lower d hd hm1 hκ
    refine ⟨p * q, (parab k _).mul_mem hp hq, w⁻¹ * z * w, (hI1 z hzl).1, ?_⟩
    have e2 : g = p * (q * z) * w := by
      rw [← e]
      group
    show g = p * q * w * (w⁻¹ * z * w)
    rw [e2]
    group
  · intro u hu
    have := hval _ ((memL u).1 hu).2
    rw [hf]
    exact this
  · intro u hu huL
    rw [hf]
    by_contra hne
    obtain ⟨p, hp, κ, hκ, e⟩ := hsup _ hne
    obtain ⟨q, hq, z, hz, hzl, rfl⟩ := exists_parab_mul_lower d hd hm1 hκ
    have hx := memU u hu
    have h1 : (w * u * w⁻¹) * z⁻¹ = 1 := by
      refine eq_one_of_mem_parab_of_mem_lower (stdBlocks d hd) ?_
        ((unipRadLower k _).mul_mem hx ((unipRadLower k _).inv_mem hzl))
      rw [e]
      have : p * (q * z) * z⁻¹ = p * q := by group
      rw [this]
      exact (parab k _).mul_mem hp hq
    have h2 : w * u * w⁻¹ = z := by rwa [mul_inv_eq_one] at h1
    exact huL ((memL u).2 ⟨hu, h2 ▸ hz⟩)

end GlobalTheory.CompanionTheory.Rodier.OpenBump

end
