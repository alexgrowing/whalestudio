import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalWhittaker
import Development.AutomorphicSpectrum.Proofs.SemilocalMultiplicity.GelfandGraevMultOneHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMirabolicWhittakerEigenspace
import Development.WeilBound.CoreStatements.RegularisedThetaMirabolic.CuspidalMirabolic.IndFacts

noncomputable section

open Matrix

namespace PositivityTheory.Mirab.Restr

section Cusp

variable {k : Type} [Field k] [Fintype k] [DecidableEq k] {N : ℕ}

def permGL (τ : Equiv.Perm (Fin N)) : GL (Fin N) k where
  val := τ.toPEquiv.toMatrix
  inv := τ.symm.toPEquiv.toMatrix
  val_inv := by
    rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_eq]
    ext i j
    simp [Matrix.one_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  inv_val := by
    rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_eq]
    ext i j
    simp [Matrix.one_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem permGL_conj (τ : Equiv.Perm (Fin N)) (M : GL (Fin N) k) :
    ((permGL τ * M * (permGL τ)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (M : Matrix (Fin N) (Fin N) k).submatrix τ τ := by
  show τ.toPEquiv.toMatrix * (M : Matrix (Fin N) (Fin N) k) * τ.symm.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem fixed_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V)
    (h : GlobalTheory.FiniteGL.IsCuspidal ρ) (s : ℕ) (b : Fin N → Fin s) (hb : Function.Surjective b) (hs : 2 ≤ s)
    (v : V) (hv : ∀ u ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip k b, ρ u v = v) : v = 0 := by
  let σ : Equiv.Perm (Fin N) := Tuple.sort b
  have hmono : Monotone (b ∘ σ) := Tuple.monotone_sort b
  let τ : Equiv.Perm (Fin N) := σ⁻¹
  let w : GL (Fin N) k := permGL τ
  let c : Fin N → ℕ := fun i => (b (σ i) : ℕ)
  have hcτ : ∀ i, c (τ i) = b i := fun i => by simp [c, τ]
  have hc : Monotone c := fun i j hij => hmono hij
  have hne : ∃ i j, c i ≠ c j := by
    obtain ⟨i, hi⟩ := hb ⟨0, by omega⟩
    obtain ⟨j, hj⟩ := hb ⟨1, by omega⟩
    refine ⟨τ i, τ j, ?_⟩
    rw [hcτ, hcτ, hi, hj]
    simp
  have key : ∀ u ∈ GlobalTheory.FiniteGL.unipRadical k c, ∀ i j, (b j : ℕ) ≤ b i →
      ((w * u * w⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = if i = j then 1 else 0 := by
    intro u hu i j hij
    have h1 := hu (τ i) (τ j) (by rw [hcτ, hcτ]; exact hij)
    rw [permGL_conj, Matrix.submatrix_apply]
    rw [Matrix.sub_apply, sub_eq_zero] at h1
    rw [h1, Matrix.one_apply]
    simp
  have hmem : ∀ u ∈ GlobalTheory.FiniteGL.unipRadical k c, w * u * w⁻¹ ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip k b := by
    intro u hu
    refine ⟨⟨fun i j hij => ?_, fun i j hij => ?_⟩, fun i j hij => ?_⟩
    · rw [key u hu i j (Nat.le_of_lt hij), if_neg]
      rintro rfl
      exact lt_irrefl _ hij
    · have e : (w * u * w⁻¹ : GL (Fin N) k)⁻¹ = w * u⁻¹ * w⁻¹ := by group
      rw [e, key u⁻¹ (inv_mem hu) i j (Nat.le_of_lt hij), if_neg]
      rintro rfl
      exact lt_irrefl _ hij
    · exact key u hu i j (by rw [hij])
  have hfix : ∀ u ∈ GlobalTheory.FiniteGL.unipRadical k c, ρ u (ρ w⁻¹ v) = ρ w⁻¹ v := by
    intro u hu
    have h1 := hv _ (hmem u hu)
    calc ρ u (ρ w⁻¹ v) = ρ w⁻¹ (ρ (w * u * w⁻¹) v) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
          congr 2
          group
      _ = ρ w⁻¹ v := by rw [h1]
  have h0 := h c hc hne _ hfix
  have h2 := congrArg (ρ w) h0
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_zero] at h2
  exact h2

theorem isCuspidal_of {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (h : GlobalTheory.FiniteGL.IsCuspidal ρ) :
    Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal k (FDRep.of ρ) :=
  fun s b hb hs v hv => fixed_eq_zero ρ h s b hb hs v hv

end Cusp

section Uni

variable {k : Type} [Field k] {d : ℕ}

abbrev upU (d : ℕ) (k : Type) [Field k] : Subgroup (GL (Fin d) k) := Formalism.L2.DIV.unip k d

theorem mem_upU {u : GL (Fin d) k} : u ∈ upU d k ↔
    (∀ i j : Fin d, j < i → (u : Matrix (Fin d) (Fin d) k) i j = 0) ∧ ∀ i, (u : Matrix (Fin d) (Fin d) k) i i = 1 :=
  Iff.rfl

def sdSum (M : Matrix (Fin d) (Fin d) k) : k := Formalism.L2.SG.GGMirabolic.superdiag d M

theorem sdSum_eq_edgeSum (g : GL (Fin d) k) :
    sdSum (g : Matrix (Fin d) (Fin d) k) = Formalism.L2.DIV.edgeSum Formalism.L2.DIV.supEdge g := by
  unfold sdSum Formalism.L2.SG.GGMirabolic.superdiag Formalism.L2.DIV.edgeSum Formalism.L2.DIV.supEdge
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (j : ℕ) = (i : ℕ) + 1 <;> simp [h]

theorem sdSum_mul {x y : GL (Fin d) k} (hx : x ∈ upU d k) (hy : y ∈ upU d k) :
    sdSum ((x * y : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) =
      sdSum (x : Matrix (Fin d) (Fin d) k) + sdSum (y : Matrix (Fin d) (Fin d) k) := by
  rw [sdSum_eq_edgeSum, sdSum_eq_edgeSum, sdSum_eq_edgeSum]
  exact GlobalTheory.FinGL.Mir.edgeSum_mul Formalism.L2.DIV.supEdge (fun _ _ h => h) hx hy

end Uni

section Wh

open ReciprocityTheory.Ty.Fin

variable {k : Type} [Field k] [Fintype k] [DecidableEq k] {d : ℕ}

def sdg (u : GL (Fin d) k) : k := sdSum (u : Matrix (Fin d) (Fin d) k)

theorem patChar_eq (ψ₀ : AddChar k ℂ) (u : GL (Fin d) k) :
    patChar (cutE k d 0) ψ₀ u = ψ₀ (sdg u) := by
  unfold patChar sdg sdSum Formalism.L2.SG.GGMirabolic.superdiag
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (j : ℕ) = i + 1
  · simp [cutE, h]
  · simp [cutE, h]

theorem patSet_eq : patSet k (fun i j : Fin d => i < j) = (upU d k : Set (GL (Fin d) k)) := by
  ext u
  rw [SetLike.mem_coe, mem_upU]
  constructor
  · intro h
    refine ⟨fun i j hij => (h i j).2 (ne_of_gt hij) (not_lt.2 hij.le), fun i => (h i i).1 rfl⟩
  · rintro ⟨h1, h2⟩ i j
    refine ⟨fun e => e ▸ h2 i, fun hne hlt => h1 i j (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))⟩

theorem wh_eq_finrank {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (GL (Fin d) k) V) (ψ₀ : AddChar k ℂ) :
    wh (fun i j : Fin d => i < j) (cutE k d 0) ψ₀ (FDRep.of ρ).character =
      Module.finrank ℂ (GlobalTheory.FinGL.eig ρ (upU d k) fun g => ψ₀ (sdg g)) := by
  classical
  haveI : Fintype (upU d k) := Fintype.ofFinite _
  have h := GlobalTheory.FinGL.Mir.card_mul_finrank_eig ρ ψ₀ (upU d k) sdg
    (fun x hx y hy => sdSum_mul hx hy)
  have hc : (Fintype.card (upU d k) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold wh
  have hn : (patSet k (fun i j : Fin d => i < j)).ncard = Fintype.card (upU d k) := by
    rw [patSet_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_eq_fintype_card
  have hs : (∑ u : GL (Fin d) k, if u ∈ patSet k (fun i j : Fin d => i < j) then
      (patChar (cutE k d 0) ψ₀ u)⁻¹ * (FDRep.of ρ).character u else 0) =
      ∑ x : upU d k, ψ₀ (-sdg (x : GL (Fin d) k)) * LinearMap.trace ℂ V (ρ x) := by
    rw [patSet_eq, ← Finset.sum_filter, Finset.sum_subtype (p := fun u => u ∈ upU d k) _ (by simp)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [patChar_eq, AddChar.map_neg_eq_inv]
    rfl
  rw [hn, hs, ← h, inv_mul_cancel_left₀ hc]

end Wh

section Whit

open ReciprocityTheory.Ty.Fin Formalism.L2.SG.GGMirabolic

variable {k : Type} [Field k] [Fintype k] [DecidableEq k] {d : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem isUni_iff (u : GL (Fin d) k) : IsUni d u ↔ u ∈ upU d k := by
  rw [mem_upU]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem psiU_eq (ψ₀ : AddChar k ℂ) (u : GL (Fin d) k) : psiU ψ₀ u = ψ₀ (sdg u) := rfl

def whProj [Fintype (upU d k)] (ρ : Representation ℂ (GL (Fin d) k) V) (ψ₀ : AddChar k ℂ) : V →ₗ[ℂ] V :=
  ∑ u : upU d k, ψ₀ (-sdg (u : GL (Fin d) k)) • ρ u

theorem whProj_comp [Fintype (upU d k)] (ρ : Representation ℂ (GL (Fin d) k) V) (ψ₀ : AddChar k ℂ)
    (u₀ : GL (Fin d) k) (h₀ : u₀ ∈ upU d k) (y : V) :
    whProj ρ ψ₀ (ρ u₀ y) = ψ₀ (sdg u₀) • whProj ρ ψ₀ y := by
  simp only [whProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight (⟨u₀, h₀⟩ : upU d k)) _ _ fun u => ?_
  have e : sdg ((u * ⟨u₀, h₀⟩ : upU d k) : GL (Fin d) k) = sdg (u : GL (Fin d) k) + sdg u₀ :=
    sdSum_mul u.2 h₀
  simp only [Equiv.coe_mulRight, e, smul_smul]
  rw [← AddChar.map_add_eq_mul, show sdg u₀ + -(sdg (u : GL (Fin d) k) + sdg u₀) = -sdg (u : GL (Fin d) k) by ring,
    Subgroup.coe_mul, map_mul, Module.End.mul_apply]

theorem whProj_eig [Fintype (upU d k)] (ρ : Representation ℂ (GL (Fin d) k) V) (ψ₀ : AddChar k ℂ) (y : V)
    (hy : y ∈ GlobalTheory.FinGL.eig ρ (upU d k) fun g => ψ₀ (sdg g)) :
    whProj ρ ψ₀ y = (Fintype.card (upU d k) : ℂ) • y := by
  rw [GlobalTheory.FinGL.Mir.mem_eig] at hy
  simp only [whProj, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl (g := fun _ => y) fun u _ => by
    rw [hy u u.2, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul]]
  rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

theorem isWhit_comp [Fintype (upU d k)] (ρ : Representation ℂ (GL (Fin d) k) V) (ψ₀ : AddChar k ℂ)
    (l : Module.Dual ℂ V) : IsWhit ψ₀ ρ (l ∘ₗ whProj ρ ψ₀) := by
  intro u hu v
  rw [LinearMap.comp_apply, whProj_comp ρ ψ₀ u ((isUni_iff u).1 hu), map_smul, psiU_eq, smul_eq_mul,
    LinearMap.comp_apply]

theorem finrank_and_whit (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) (ρ : Representation ℂ (GL (Fin d) k) V)
    (hi : ρ.IsIrreducible) (hc : GlobalTheory.FiniteGL.IsCuspidal ρ) :
    (Module.finrank ℂ V : ℂ) = ∏ i ∈ Finset.Ico 1 d, ((Fintype.card k : ℂ) ^ i - 1) ∧
      ∃ L : Module.Dual ℂ V, L ≠ 0 ∧ IsWhit ψ₀ ρ L := by
  classical
  haveI : Fintype (upU d k) := Fintype.ofFinite _
  have hcard : (Fintype.card (upU d k) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hW : (Module.finrank ℂ V : ℂ) = _ * _ :=
    GlobalTheory.CompanionTheory.TyFin.ColStep.cuspWh k d ψ₀ (FDRep.of ρ) hψ (isCuspidal_of ρ hc)
  rw [wh_eq_finrank] at hW
  set D := GlobalTheory.FinGL.eig ρ (upU d k) fun g => ψ₀ (sdg g) with hD
  haveI : Nontrivial V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have hb : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
    exact bot_ne_top hb
  have hV0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hD0 : Module.finrank ℂ D ≠ 0 := by
    intro h0
    rw [h0] at hW
    exact hV0 (by simpa using hW)
  have hDbot : D ≠ ⊥ := fun h0 => hD0 (by rw [h0]; simp)
  obtain ⟨x, hxD, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hDbot
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual ℂ V, l x ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff ℂ x).1 hn)
  set L : Module.Dual ℂ V := l ∘ₗ whProj ρ ψ₀ with hLdef
  have hLx : L x ≠ 0 := by
    rw [hLdef, LinearMap.comp_apply, whProj_eig ρ ψ₀ x hxD, map_smul, smul_eq_mul]
    exact mul_ne_zero hcard hl
  have hL0 : L ≠ 0 := fun h0 => hLx (by rw [h0]; rfl)
  have hLw : IsWhit ψ₀ ρ L := isWhit_comp ρ ψ₀ l
  have hinj : Function.Injective (L ∘ₗ D.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨y, hy⟩ hy0
    have hy0' : L y = 0 := hy0
    have hall : ∀ l' : Module.Dual ℂ V, l' y = 0 := by
      intro l'
      obtain ⟨c, hc'⟩ := GlobalTheory.CompanionTheory.GG.gelfandGraevMultOne_holds k d ψ₀ hψ V ρ hi L (l' ∘ₗ whProj ρ ψ₀) hLw
        (isWhit_comp ρ ψ₀ l') hL0
      have h1 := LinearMap.congr_fun hc' y
      rw [LinearMap.comp_apply, whProj_eig ρ ψ₀ y hy, map_smul, LinearMap.smul_apply, hy0', smul_zero, smul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left hcard
    exact Subtype.ext ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hall)
  have hD1 : Module.finrank ℂ D = 1 := by
    have h1 := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_self] at h1
    omega
  refine ⟨?_, L, hL0, hLw⟩
  rw [hD1] at hW
  simpa using hW

end Whit

section Main

open Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling Formalism.L2.SG.GGMirabolic

variable {k : Type} [Field k] [Fintype k] [DecidableEq k] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem sdSum_eq_supd (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : sdSum M = supd M := by
  unfold sdSum superdiag supd
  rw [Fin.sum_univ_castSucc]
  have hl : (∑ j : Fin (n + 1), if (j : ℕ) = ((Fin.last n : Fin (n + 1)) : ℕ) + 1 then M (Fin.last n) j else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => if_neg (by have := j.2; simp; omega)
  rw [hl, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    exact if_neg fun e => hj (Fin.ext (by simpa using e))
  · simp

def whitMap (ψ₀ : AddChar k ℂ) (ρ : Representation ℂ (GL (Fin (n + 1)) k) V) (L : Module.Dual ℂ V)
    (hL : IsWhit ψ₀ ρ L) : V →ₗ[ℂ] GlobalTheory.FiniteGL.MirabInducedSpace n ψ₀ where
  toFun x := ⟨fun p => L (ρ (p : GL (Fin (n + 1)) k) x), by
    rw [GlobalTheory.FiniteGL.mem_mirabInducedSpace]
    intro u p
    have hu : IsUni (n + 1) ((u : mirabSub k n) : GL (Fin (n + 1)) k) := ⟨u.2.1, u.2.2⟩
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hL _ hu, psiU_eq, GlobalTheory.FiniteGL.genericChar_apply, sdg,
      sdSum_eq_supd]⟩
  map_add' x y := Subtype.ext (funext fun p => by simp)
  map_smul' c x := Subtype.ext (funext fun p => by simp)

end Main

theorem cuspidalRestrictsToInduced : GlobalTheory.Published.CuspidalRestrictsToInduced := by
  intro k _ _ n ψ₀ hψ V _ _ _ ρ hi hc
  classical
  obtain ⟨hdim, L, hL0, hLw⟩ := finrank_and_whit ψ₀ hψ ρ hi hc
  let T := whitMap ψ₀ ρ L hLw
  let W : Subrepresentation (GlobalTheory.FiniteGL.mirabInduced n ψ₀) :=
    ⟨LinearMap.range T, by
      rintro q _ ⟨x, rfl⟩
      refine ⟨ρ (q : GL (Fin (n + 1)) k) x, Subtype.ext (funext fun y => ?_)⟩
      show L (ρ (y : GL (Fin (n + 1)) k) (ρ (q : GL (Fin (n + 1)) k) x)) =
        L (ρ ((y * q : Formalism.L2.Indef.Tree.mirabSub k n) : GL (Fin (n + 1)) k) x)
      rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  have hirr := PositivityTheory.Mirab.mirabInduced_isIrreducible n ψ₀ hψ
  have hsurj : Function.Surjective T := by
    rcases hirr.eq_bot_or_eq_top W with hW | hW
    · exfalso
      refine hL0 (LinearMap.ext fun x => ?_)
      have h1 : T x ∈ (⊥ : Submodule ℂ _) := by
        have : T x ∈ W.toSubmodule := ⟨x, rfl⟩
        rw [hW] at this
        exact this
      have h2 := congrFun (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h1)) 1
      have h3 : L (ρ 1 x) = 0 := h2
      simpa using h3
    · have h1 : LinearMap.range T = ⊤ := congrArg Subrepresentation.toSubmodule hW
      exact LinearMap.range_eq_top.1 h1
  have hfin : Module.finrank ℂ V = Module.finrank ℂ (GlobalTheory.FiniteGL.MirabInducedSpace n ψ₀) := by
    rw [PositivityTheory.Mirab.finrank_mirabInducedSpace]
    have h2 : (Module.finrank ℂ V : ℂ) = ((∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) : ℕ) : ℂ) := by
      rw [hdim, Nat.cast_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos), Nat.cast_pow, Nat.cast_one]
    exact_mod_cast h2
  have hinj : Function.Injective T := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurj
  let E : V ≃ₗ[ℂ] GlobalTheory.FiniteGL.MirabInducedSpace n ψ₀ := LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
  have hint : ∀ g, T ∘ₗ GlobalTheory.FiniteGL.restrictMirab n ρ g = GlobalTheory.FiniteGL.mirabInduced n ψ₀ g ∘ₗ T := by
    intro g
    refine LinearMap.ext fun x => Subtype.ext (funext fun y => ?_)
    show L (ρ (y : GL (Fin (n + 1)) k) (ρ (g : GL (Fin (n + 1)) k) x)) =
      L (ρ ((y * g : Formalism.L2.Indef.Tree.mirabSub k n) : GL (Fin (n + 1)) k) x)
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  exact ⟨{ toIntertwiningMap := ⟨T, hint⟩
           invFun := E.symm
           left_inv := E.left_inv
           right_inv := E.right_inv }⟩

end PositivityTheory.Mirab.Restr
