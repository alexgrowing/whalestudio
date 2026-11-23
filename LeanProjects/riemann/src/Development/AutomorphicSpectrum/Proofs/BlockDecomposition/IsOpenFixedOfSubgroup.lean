import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirProj
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import GroundTheory.AutomorphicForms.LocallyProfinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMirOnto

theorem exists_fixed_lift {L W W' : Type} [Group L] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ L W) (ρ' : Representation ℂ L W') (f : W →ₗ[ℂ] W')
    (hf : ∀ x w, f (ρ x w) = ρ' x (f w)) (S : Subgroup L) [Finite (L ⧸ S)] (w : W)
    (hS : ∀ s ∈ S, ρ s w = w) (hw : ∀ l, ρ' l (f w) = f w) :
    ∃ w₁, f w₁ = f w ∧ ∀ l, ρ l w₁ = w₁ := by
  classical
  haveI := Fintype.ofFinite (L ⧸ S)
  let φ : L ⧸ S → W := fun x => ρ x.out w
  have key : ∀ (l : L) (x : L ⧸ S), ρ l (φ x) = φ (l • x) := by
    intro l x
    have e : ((l * x.out : L) : L ⧸ S) = l • x := by
      conv_rhs => rw [← QuotientGroup.out_eq' x]
      rfl
    have e2 : (l • x).out⁻¹ * (l * x.out) ∈ S := by
      apply QuotientGroup.eq.1
      rw [e, QuotientGroup.out_eq']
    have := hS _ e2
    rw [map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply] at this
    show ρ l (ρ x.out w) = ρ (l • x).out w
    calc ρ l (ρ x.out w) = ρ (l • x).out (ρ (l • x).out⁻¹ (ρ l (ρ x.out w))) := by
          rw [← Module.End.mul_apply (ρ (l • x).out), ← map_mul]; simp
      _ = ρ (l • x).out w := by rw [this]
  have hc : ((Fintype.card (L ⧸ S) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨((Fintype.card (L ⧸ S) : ℕ) : ℂ)⁻¹ • ∑ x, φ x, ?_, fun l => ?_⟩
  · rw [map_smul, map_sum]
    have : ∀ x, f (φ x) = f w := fun x => by
      show f (ρ x.out w) = f w
      rw [hf, hw]
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rw [map_smul, map_sum]
    simp only [key]
    congr 1
    exact Equiv.sum_comp (MulAction.toPerm l) φ

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem isOpen_fixed_of_subgroup {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (v : V) (h : ∀ x ∈ K, ρ x v = v) : IsOpen {g : G | ρ g v = v} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hn : (fun y => g⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 g :=
    (hK.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
  filter_upwards [hn] with y hy
  have e : y = g * (g⁻¹ * y) := by group
  show ρ y v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hy]
  exact hg

theorem exists_bump (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (c : G) (w : W)
    (hw : ∀ a : H, ∀ x ∈ K, (a : G) = c * x * c⁻¹ → ρ a w = w) :
    ∃ B : cIndSpace H ρ, (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * c * x) = ρ a w) ∧
      ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * c * x) → B.1.1.1 g = 0 := by
  classical
  let b : G → W := fun g => if h : ∃ a : H, ∃ x ∈ K, g = (a : G) * c * x then ρ h.choose w else 0
  have hb1 : ∀ (a : H), ∀ x ∈ K, b ((a : G) * c * x) = ρ a w := by
    intro a x hx
    have h : ∃ a' : H, ∃ x' ∈ K, (a : G) * c * x = (a' : G) * c * x' := ⟨a, x, hx, rfl⟩
    simp only [b, dif_pos h]
    obtain ⟨x', hx', e⟩ := h.choose_spec
    generalize h.choose = a' at e ⊢
    have e2 : ((a'⁻¹ * a : H) : G) = c * (x' * x⁻¹) * c⁻¹ := by
      have e3 : (a : G) = a' * c * x' * x⁻¹ * c⁻¹ := by rw [← e]; group
      push_cast
      rw [e3]
      group
    have e4 := hw (a'⁻¹ * a) _ (mul_mem hx' (inv_mem hx)) e2
    rw [map_mul, Module.End.mul_apply] at e4
    calc ρ a' w = ρ a' (ρ a'⁻¹ (ρ a w)) := by rw [e4]
      _ = ρ a w := by rw [← Module.End.mul_apply (ρ a'), ← map_mul]; simp
  have hb0 : ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * c * x) → b g = 0 := fun g h => dif_neg h
  have hind : b ∈ indSpace H ρ := by
    intro h g
    by_cases hg : ∃ a : H, ∃ x ∈ K, g = (a : G) * c * x
    · obtain ⟨a, x, hx, rfl⟩ := hg
      have e : (h : G) * ((a : G) * c * x) = ((h * a : H) : G) * c * x := by push_cast; group
      rw [e, hb1 _ _ hx, hb1 _ _ hx, map_mul, Module.End.mul_apply]
    · have hn : ¬ ∃ a : H, ∃ x ∈ K, (h : G) * g = (a : G) * c * x := by
        rintro ⟨a, x, hx, e⟩
        refine hg ⟨h⁻¹ * a, x, hx, ?_⟩
        have : g = (h : G)⁻¹ * ((h : G) * g) := by group
        rw [this, e]
        push_cast
        group
      rw [hb0 _ hn, hb0 _ hg, map_zero]
  have hinv : ∀ g, ∀ y ∈ K, b (g * y) = b g := by
    intro g y hy
    by_cases hg : ∃ a : H, ∃ x ∈ K, g = (a : G) * c * x
    · obtain ⟨a, x, hx, rfl⟩ := hg
      rw [mul_assoc, hb1 _ _ hx, hb1 _ _ (mul_mem hx hy)]
    · have hn : ¬ ∃ a : H, ∃ x ∈ K, g * y = (a : G) * c * x := by
        rintro ⟨a, x, hx, e⟩
        refine hg ⟨a, x * y⁻¹, mul_mem hx (inv_mem hy), ?_⟩
        rw [← mul_assoc, ← e]
        group
      rw [hb0 _ hn, hb0 _ hg]
  have hsm : (⟨b, hind⟩ : indSpace H ρ) ∈ smoothPart (ind H ρ) := by
    refine isOpen_fixed_of_subgroup (ind H ρ) K hKo _ fun x hx => ?_
    apply Subtype.ext
    funext g
    exact hinv g x hx
  have hc : (⟨⟨b, hind⟩, hsm⟩ : smoothPart (ind H ρ)) ∈ cIndSpace H ρ := by
    refine ⟨(fun x => c * x) '' K, hKc.image (by fun_prop), fun g hg => ?_⟩
    have hg' : b g ≠ 0 := hg
    by_contra hcon
    apply hg'
    apply hb0
    rintro ⟨a, x, hx, e⟩
    exact hcon ⟨a, a.2, c * x, ⟨x, hx, rfl⟩, by rw [e, mul_assoc]⟩
  exact ⟨⟨⟨⟨b, hind⟩, hsm⟩, hc⟩, hb1, hb0⟩

theorem exists_lift_at (H : Subgroup G) (hH : IsClosed (H : Set G)) (ρ : Representation ℂ H W)
    (ρ' : Representation ℂ H W') (f : W →ₗ[ℂ] W') (hsurj : Function.Surjective f)
    (hf : ∀ x w, f (ρ x w) = ρ' x (f w))
    (hstab : ∀ w, f w ≠ 0 → ∃ S : Subgroup H, IsOpen (S : Set H) ∧ ∀ s ∈ S, ρ' s (f w) = f w → ρ s w = w)
    (K : Subgroup G) (hKc : IsCompact (K : Set G)) (c : G) (y : W')
    (hy : ∀ a : H, ∀ x ∈ K, (a : G) = c * x * c⁻¹ → ρ' a y = y) :
    ∃ w, f w = y ∧ ∀ a : H, ∀ x ∈ K, (a : G) = c * x * c⁻¹ → ρ a w = w := by
  by_cases hy0 : y = 0
  · exact ⟨0, by simp [hy0], fun a x _ _ => map_zero _⟩
  obtain ⟨w₀, rfl⟩ := hsurj y
  obtain ⟨S, hSo, hS⟩ := hstab w₀ hy0
  let L : Subgroup H := (K.map (MulAut.conj c).toMonoidHom).comap H.subtype
  have hLmem : ∀ l : L, ∃ x ∈ K, ((l : H) : G) = c * x * c⁻¹ := by
    intro l
    obtain ⟨x, hx, e⟩ := l.2
    exact ⟨x, hx, e.symm⟩
  have hLc : IsCompact (L : Set H) := by
    have h1 : IsCompact ((fun x => c * x * c⁻¹) '' (K : Set G)) := hKc.image (by fun_prop)
    have h2 : Topology.IsClosedEmbedding (H.subtype : H → G) := hH.isClosedEmbedding_subtypeVal
    convert h2.isCompact_preimage h1 using 1
    ext l
    constructor
    · rintro ⟨x, hx, e⟩
      exact ⟨x, hx, e⟩
    · rintro ⟨x, hx, e⟩
      exact ⟨x, hx, e⟩
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  let S' : Subgroup L := S.subgroupOf L
  have hS'o : IsOpen (S' : Set L) := hSo.preimage continuous_subtype_val
  haveI : Finite (L ⧸ S') := Subgroup.quotient_finite_of_isOpen _ hS'o
  have hfix : ∀ l : L, ρ' (l : H) (f w₀) = f w₀ := fun l => by
    obtain ⟨x, hx, e⟩ := hLmem l
    exact hy _ x hx e
  obtain ⟨w₁, h1, h2⟩ := exists_fixed_lift (ρ.comp L.subtype) (ρ'.comp L.subtype) f (fun x w => hf x w) S' w₀
    (fun s hs => hS _ hs (hfix s)) hfix
  refine ⟨w₁, h1, fun a x hx e => ?_⟩
  have ha : a ∈ L := ⟨x, hx, e.symm⟩
  exact h2 ⟨a, ha⟩

theorem cInd_lift (H : Subgroup G) (hH : IsClosed (H : Set G))
    (hbasis : ∀ U : Set G, U ∈ 𝓝 (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W') (f : W →ₗ[ℂ] W') (hsurj : Function.Surjective f)
    (hf : ∀ x w, f (ρ x w) = ρ' x (f w))
    (hstab : ∀ w, f w ≠ 0 → ∃ S : Subgroup H, IsOpen (S : Set H) ∧ ∀ s ∈ S, ρ' s (f w) = f w → ρ s w = w)
    (F : cIndSpace H ρ') : ∃ F' : cIndSpace H ρ, ∀ g, f (F'.1.1.1 g) = F.1.1.1 g := by
  classical
  obtain ⟨C, hC, hsupp⟩ := F.2
  have hFo : IsOpen {g : G | ind H ρ' g F.1.1 = F.1.1} := F.1.2
  obtain ⟨K, hKo, hKc, hKU⟩ := hbasis _ (hFo.mem_nhds (by simp))
  have hKinv : ∀ g, ∀ x ∈ K, F.1.1.1 (g * x) = F.1.1.1 g := by
    intro g x hx
    have h : ind H ρ' x F.1.1 = F.1.1 := hKU hx
    exact congrArg (fun v : indSpace H ρ' => v.1 g) h
  have hFeq : ∀ (a : H) (g : G), F.1.1.1 ((a : G) * g) = ρ' a (F.1.1.1 g) := F.1.1.2
  have hlift : ∀ c : G, ∃ w, f w = F.1.1.1 c ∧ ∀ a : H, ∀ x ∈ K, (a : G) = c * x * c⁻¹ → ρ a w = w := by
    intro c
    refine exists_lift_at H hH ρ ρ' f hsurj hf hstab K hKc c _ fun a x hx e => ?_
    rw [← hFeq, e]
    have : c * x * c⁻¹ * c = c * x := by group
    rw [this, hKinv _ _ hx]
  choose w hw1 hw2 using hlift
  have hbump := fun c : G => exists_bump H ρ K hKo hKc c (w c) (hw2 c)
  choose B hB1 hB0 using hbump
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K : Set G)) (fun c _ => by
    have : (fun y => c⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 c :=
      (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
    filter_upwards [this] with y hy
    exact ⟨c⁻¹ * y, hy, by group⟩)
  let T : Finset (DoubleCoset.Quotient (H : Set G) (K : Set G)) := t.image (DoubleCoset.mk H K)
  have hoff : ∀ (d : DoubleCoset.Quotient (H : Set G) (K : Set G)) (g : G), DoubleCoset.mk H K g ≠ d →
      (B (Quotient.out d)).1.1.1 g = 0 := by
    intro d g hne
    apply hB0
    rintro ⟨a, x, hx, e⟩
    apply hne
    rw [← DoubleCoset.out_eq' H K d]
    exact ((DoubleCoset.eq H K _ _).2 ⟨a, a.2, x, hx, e⟩).symm
  refine ⟨∑ d ∈ T, B (Quotient.out d), fun g => ?_⟩
  let ev : cIndSpace H ρ →ₗ[ℂ] W :=
    (LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ (cIndSpace H ρ).subtype
  have hsum : (∑ d ∈ T, B (Quotient.out d)).1.1.1 g = ∑ d ∈ T, (B (Quotient.out d)).1.1.1 g :=
    map_sum ev _ _
  rw [hsum]
  by_cases hg : DoubleCoset.mk H K g ∈ T
  · rw [Finset.sum_eq_single_of_mem _ hg (fun d _ hd => hoff d g (Ne.symm hd))]
    obtain ⟨a, ha, x, hx, e⟩ := (DoubleCoset.eq H K _ _).1 (DoubleCoset.out_eq' H K (DoubleCoset.mk H K g))
    have e' : g = ((⟨a, ha⟩ : H) : G) * Quotient.out (DoubleCoset.mk H K g) * x := e
    generalize Quotient.out (DoubleCoset.mk H K g) = c at e'
    rw [e', hB1 _ _ _ hx, hf, hw1, hKinv _ _ hx, hFeq]
  · rw [Finset.sum_eq_zero (fun d hd => hoff d g (fun h => hg (h ▸ hd))), map_zero]
    by_contra hne
    obtain ⟨a, ha, c', hc', e⟩ := hsupp g (Ne.symm hne)
    obtain ⟨c, hc, hcc⟩ := Set.mem_iUnion₂.1 (ht hc')
    obtain ⟨x, hx, rfl⟩ := hcc
    apply hg
    have : DoubleCoset.mk H K c = DoubleCoset.mk H K g :=
      (DoubleCoset.eq H K _ _).2 ⟨a, ha, x, hx, by rw [e]; group⟩
    rw [← this]
    exact Finset.mem_image_of_mem _ hc

end General

section Mirabolic

open GlobalTheory.SplitWeil.Model

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isClosed_Mir (n : ℕ) : IsClosed (Mir k n : Set (GL (Fin (n + 1)) k)) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have e : (Mir k n : Set (GL (Fin (n + 1)) k)) =
      {g : GL (Fin (n + 1)) k | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) = eLast k n} :=
    Set.ext fun g => mem_Mir_iff k g
  rw [e]
  have hval : Continuous fun g : GL (Fin (n + 1)) k => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := Units.continuous_val
  exact isClosed_eq (continuous_pi fun j => (continuous_apply j).comp ((continuous_apply (Fin.last n)).comp hval))
    continuous_const

theorem continuous_qProj (n : ℕ) : Continuous (qProj k n) :=
  Continuous.subtype_mk ((GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k (n + 1)).comp continuous_subtype_val) _

theorem exists_compactOpen (n : ℕ) (U : Set (Mir k n)) (hU : U ∈ 𝓝 (1 : Mir k n)) :
    ∃ K : Subgroup (Mir k n), IsOpen (K : Set (Mir k n)) ∧ IsCompact (K : Set (Mir k n)) ∧ (K : Set (Mir k n)) ⊆ U := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  haveI : LocallyCompactSpace (Mir k n) := (isClosed_Mir k n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin (n + 1) → Fin (n + 1) → k))
  haveI : TotallyDisconnectedSpace (Mir k n) := by
    let φ : Mir k n → Matrix (Fin (n + 1)) (Fin (n + 1)) k := fun g => ((g : GL (Fin (n + 1)) k) : Matrix _ _ k)
    have hφ : Continuous φ := Units.continuous_val.comp continuous_subtype_val
    have hinj : Function.Injective φ := fun a b h => Subtype.ext (Units.ext h)
    exact ⟨isTotallyDisconnected_of_image hφ.continuousOn hinj (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  obtain ⟨K, hKc, hKU⟩ := GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset hU
  exact ⟨K.toSubgroup, K.isOpen, hKc, hKU⟩

end Mirabolic

end GlobalTheory.CompanionTheory.BZMirOnto
