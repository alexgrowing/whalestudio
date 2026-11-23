import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaC
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CountClosedComm

theorem relIndex_ne_zero_of_cover {G : Type} [Group G] (M W : Subgroup G) (S : Set G) (hS : S.Finite)
    (h : ∀ w ∈ W, ∃ s ∈ S, s⁻¹ * w ∈ M) : M.relIndex W ≠ 0 := by
  have hfin : Finite S := hS.to_subtype
  choose φ hφ hφM using h
  let ψ : W ⧸ M.subgroupOf W → S := fun q => ⟨φ q.out q.out.2, hφ _ q.out.2⟩
  have hinj : Function.Injective ψ := by
    intro q q' hqq
    have e : φ q.out q.out.2 = φ q'.out q'.out.2 := congrArg Subtype.val hqq
    have a := hφM _ q.out.2
    have b := hφM _ q'.out.2
    rw [← e] at b
    have hm : (q.out)⁻¹ * q'.out ∈ M.subgroupOf W := by
      rw [Subgroup.mem_subgroupOf]
      have := M.mul_mem (M.inv_mem a) b
      simpa [mul_assoc] using this
    calc q = QuotientGroup.mk q.out := (QuotientGroup.out_eq' q).symm
      _ = QuotientGroup.mk q'.out := QuotientGroup.eq.2 hm
      _ = q' := QuotientGroup.out_eq' q'
  have : Finite (W ⧸ M.subgroupOf W) := Finite.of_injective ψ hinj
  exact Subgroup.index_ne_zero_of_finite

theorem exists_pow_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (L : Subgroup G)
    (hL : IsOpen (L : Set G)) (t : G) (hc : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    ∃ k : ℕ, 0 < k ∧ t ^ k ∈ L :=
  _root_.Bl.FirstLemmaC.goal1 L hL t hc

theorem cover_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (L T Γ : Subgroup G) (C : Set G) (hLo : IsOpen (L : Set G)) (hTc : IsClosed (T : Set G)) (hΓ : Γ ≤ T)
    (hC : IsCompact C) (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c) :
    ∃ F : Finset G, (∀ f ∈ F, f ∈ T) ∧ ∀ t ∈ T, ∃ γ ∈ Γ, ∃ f ∈ F, ∃ m ∈ T ⊓ L, t = γ * f * m := by
  have hTC : IsCompact ((T : Set G) ∩ C) := hC.inter_left hTc
  obtain ⟨F, hF, hU⟩ := hTC.elim_nhds_subcover (fun z => {g | z⁻¹ * g ∈ (L : Set G)}) (fun z _ =>
    IsOpen.mem_nhds (hLo.preimage (continuous_const.mul continuous_id)) (by simp [L.one_mem]))
  refine ⟨F, fun f hf => (hF f hf).1, ?_⟩
  intro t ht
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov t ht
  have hcT : c ∈ T := by
    have := T.mul_mem (T.inv_mem (hΓ hγ)) ht
    simpa using this
  obtain ⟨f, hf, hcf⟩ := Set.mem_iUnion₂.1 (hU ⟨hcT, hc⟩)
  exact ⟨γ, hγ, f, hf, f⁻¹ * c, ⟨T.mul_mem (T.inv_mem (hF f hf).1) hcT, hcf⟩, by group⟩

def powRad {G : Type} [Group G] (T M : Subgroup G) (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : Subgroup G where
  carrier := {t | t ∈ T ∧ ∃ k : ℕ, 0 < k ∧ t ^ k ∈ M}
  mul_mem' := by
    rintro a b ⟨ha, k, hk, hak⟩ ⟨hb, l, hl, hbl⟩
    refine ⟨T.mul_mem ha hb, k * l, Nat.mul_pos hk hl, ?_⟩
    have hc : Commute a b := hcomm a ha b hb
    rw [hc.mul_pow, pow_mul a, pow_mul' b]
    exact M.mul_mem (M.pow_mem hak _) (M.pow_mem hbl _)
  one_mem' := ⟨T.one_mem, 1, one_pos, by simp [M.one_mem]⟩
  inv_mem' := by
    rintro a ⟨ha, k, hk, hak⟩
    exact ⟨T.inv_mem ha, k, hk, by rw [inv_pow]; exact M.inv_mem hak⟩

theorem le_powRad {G : Type} [Group G] (T M : Subgroup G) (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hM : M ≤ T) : M ≤ powRad T M hcomm :=
  fun m hm => ⟨hM hm, 1, one_pos, by simpa using hm⟩

theorem cptPart_le_powRad {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (T L : Subgroup G) (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hLo : IsOpen (L : Set G)) :
    cptPart T ≤ powRad T (T ⊓ L) hcomm := by
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨ht, hc⟩
  obtain ⟨k, hk, hkL⟩ := exists_pow_mem L hLo t hc
  exact ⟨ht, k, hk, T.pow_mem ht k, hkL⟩

theorem inf_le_cptPart' {G : Type} [Group G] [TopologicalSpace G] [T2Space G] (T L : Subgroup G)
    (hL : IsCompact (L : Set G)) : T ⊓ L ≤ cptPart T := by
  intro t ht
  apply Subgroup.subset_closure
  refine ⟨ht.1, hL.of_isClosed_subset isClosed_closure ?_⟩
  exact closure_minimal (fun x hx => (Subgroup.zpowers_le.2 ht.2) hx) hL.isClosed

theorem isOfFinOrder_of_pow_mem {G : Type} [Group G] (Γ M : Subgroup G)
    (hfin : ((Γ : Set G) ∩ (M : Set G)).Finite) (γ : G) (hγ : γ ∈ Γ) (k : ℕ) (hk : 0 < k) (hkM : γ ^ k ∈ M) :
    IsOfFinOrder γ := by
  have h : IsOfFinOrder (γ ^ k) := by
    rw [← finite_powers]
    refine hfin.subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨Γ.pow_mem (Γ.pow_mem hγ k) n, M.pow_mem hkM n⟩
  exact h.of_pow hk.ne'

theorem relIndex_ne_zero_of_torsion {G : Type} [Group G] (T M W Γ : Subgroup G)
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hMT : M ≤ T) (hMW : M ≤ W) (hΓ : Γ ≤ T)
    (F : Finset G) (hF : ∀ f ∈ F, f ∈ T) (hWT : W ≤ T)
    (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ f ∈ F, ∃ m ∈ M, t = γ * f * m)
    (Tor : Set G) (hTor : Tor.Finite) (hsub : ∀ σ ∈ Γ, σ ∈ W → σ ∈ Tor) : M.relIndex W ≠ 0 := by
  have hr : ∀ f : G, ∃ r : G, (∃ t ∈ W, ∃ γ ∈ Γ, ∃ m ∈ M, t = γ * f * m) →
      r ∈ W ∧ ∃ γ ∈ Γ, ∃ m ∈ M, r = γ * f * m := by
    intro f
    by_cases h : ∃ t ∈ W, ∃ γ ∈ Γ, ∃ m ∈ M, t = γ * f * m
    · obtain ⟨t, ht, hh⟩ := h
      exact ⟨t, fun _ => ⟨ht, hh⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose r hr using hr
  refine relIndex_ne_zero_of_cover M W (Set.image2 (fun f σ => r f * σ) (F : Set G) Tor)
    (Set.Finite.image2 _ F.finite_toSet hTor) ?_
  intro w hw
  obtain ⟨a, ha, f, hf, c, hc, rfl⟩ := hcov w (hWT hw)
  obtain ⟨hrW, d, hd, e, he, hrf⟩ := hr f ⟨_, hw, a, ha, c, hc, rfl⟩
  have hσT : d⁻¹ * a ∈ T := T.mul_mem (T.inv_mem (hΓ hd)) (hΓ ha)
  have hσΓ : d⁻¹ * a ∈ Γ := Γ.mul_mem (Γ.inv_mem hd) ha
  have h1 : (r f)⁻¹ * (a * f * c) = e⁻¹ * (d⁻¹ * a) * c := by
    have hb : f * (d⁻¹ * a) = (d⁻¹ * a) * f := hcomm _ (hF f hf) _ hσT
    have hb' : f⁻¹ * (d⁻¹ * a) * f = d⁻¹ * a := by rw [mul_assoc, ← hb]; group
    rw [hrf]
    calc (d * f * e)⁻¹ * (a * f * c) = e⁻¹ * (f⁻¹ * (d⁻¹ * a) * f) * c := by group
      _ = e⁻¹ * (d⁻¹ * a) * c := by rw [hb']
  have hσW : d⁻¹ * a ∈ W := by
    have h2 : d⁻¹ * a = e * ((r f)⁻¹ * (a * f * c)) * c⁻¹ := by rw [h1]; group
    rw [h2]
    exact W.mul_mem (W.mul_mem (hMW he) (W.mul_mem (W.inv_mem hrW) hw)) (W.inv_mem (hMW hc))
  refine ⟨r f * (d⁻¹ * a), ⟨f, hf, d⁻¹ * a, hsub _ hσΓ hσW, rfl⟩, ?_⟩
  have hcm : e⁻¹ * (d⁻¹ * a) = (d⁻¹ * a) * e⁻¹ := hcomm _ (T.inv_mem (hMT he)) _ hσT
  have h3 : (r f * (d⁻¹ * a))⁻¹ * (a * f * c) = e⁻¹ * c := by
    rw [_root_.mul_inv_rev, mul_assoc, h1, hcm]
    group
  rw [h3]
  exact M.mul_mem (M.inv_mem he) hc

theorem isCompact_inf {G : Type} [Group G] [TopologicalSpace G] [T2Space G] (T L : Subgroup G)
    (hTc : IsClosed (T : Set G)) (hL : IsCompact (L : Set G)) : IsCompact ((T ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  exact hL.inter_left hTc

theorem part {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (L T Γ : Subgroup G)
    (C : Set G) (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G)) (hTc : IsClosed (T : Set G))
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hΓ : Γ ≤ T) (hC : IsCompact C)
    (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c)
    (hfin : ∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) (htor : {γ : G | γ ∈ Γ ∧ IsOfFinOrder γ}.Finite) :
    (T ⊓ L).relIndex (cptPart T) ≠ 0 ∧ Finite (Γ ⊓ cptPart T : Subgroup G) := by
  set M := T ⊓ L with hM
  have hMT : M ≤ T := inf_le_left
  have hsub : ∀ σ ∈ Γ, σ ∈ powRad T M hcomm → σ ∈ {γ : G | γ ∈ Γ ∧ IsOfFinOrder γ} := by
    rintro σ hσ ⟨-, k, hk, hkM⟩
    exact ⟨hσ, isOfFinOrder_of_pow_mem Γ M (hfin _ (isCompact_inf T L hTc hLc)) σ hσ k hk hkM⟩
  have hle : cptPart T ≤ powRad T M hcomm := cptPart_le_powRad T L hcomm hLo
  obtain ⟨F, hF, hcovF⟩ := cover_cosets L T Γ C hLo hTc hΓ hC hcov
  refine ⟨?_, ?_⟩
  · have hW : M.relIndex (powRad T M hcomm) ≠ 0 :=
      relIndex_ne_zero_of_torsion T M (powRad T M hcomm) Γ hcomm hMT (le_powRad T M hcomm hMT) hΓ F hF
        (fun _ h => h.1) hcovF _ htor hsub
    exact fun h0 => hW (Subgroup.relIndex_eq_zero_of_le_right hle h0)
  · have : ((Γ ⊓ cptPart T : Subgroup G) : Set G).Finite :=
      htor.subset fun σ hσ => hsub σ hσ.1 (hle hσ.2)
    exact this.to_subtype

theorem finite_doubleCoset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (L T Γ : Subgroup G) (C : Set G) (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G))
    (hTc : IsClosed (T : Set G)) (hΓ : Γ ≤ T) (hC : IsCompact C)
    (hcov : ∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c) :
    Finite (DoubleCoset.Quotient (((Γ.subgroupOf T) : Subgroup T) : Set T)
      (((cptPart T).subgroupOf T : Subgroup T) : Set T)) := by
  obtain ⟨F, hF, hcovF⟩ := cover_cosets L T Γ C hLo hTc hΓ hC hcov
  let φ : F → DoubleCoset.Quotient (((Γ.subgroupOf T) : Subgroup T) : Set T)
      (((cptPart T).subgroupOf T : Subgroup T) : Set T) :=
    fun f => DoubleCoset.mk _ _ ⟨f.1, hF f.1 f.2⟩
  refine Finite.of_surjective φ fun q => ?_
  induction q using Quotient.inductionOn' with
  | h t =>
    obtain ⟨γ, hγ, f, hf, m, hm, ht⟩ := hcovF t.1 t.2
    refine ⟨⟨f, hf⟩, ?_⟩
    refine Quotient.sound' ?_
    rw [DoubleCoset.rel_iff]
    refine ⟨⟨γ, hΓ hγ⟩, ?_, ⟨m, hm.1⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 hγ
    · exact Subgroup.mem_subgroupOf.2 (inf_le_cptPart' T L hLc hm)
    · apply Subtype.ext
      simp [ht, mul_assoc]

theorem main : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (K T Γ : Subgroup G) (C : Set G),
  IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (T : Set G) → (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → Γ ≤ T →
  IsCompact C → (∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c) →
  (∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) → {γ : G | γ ∈ Γ ∧ IsOfFinOrder γ}.Finite →
  (∀ x : G, T ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart T ∧
    (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart T) ≠ 0) ∧
  (∀ x : G, Finite (Γ ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)) ∧
  Finite (Γ ⊓ cptPart T : Subgroup G) ∧
  Finite (DoubleCoset.Quotient (((Γ.subgroupOf T) : Subgroup T) : Set T) (((cptPart T).subgroupOf T : Subgroup T) : Set T)) := by
  intro G _ _ _ _ K T Γ C hKo hKc hTc hcomm hΓ hC hcov hfin htor
  have hLo : ∀ x : G, IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    intro x
    have : ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) = (Homeomorph.mulRight x⁻¹ ∘ Homeomorph.mulLeft x) '' (K : Set G) := by
      ext g; simp [MulAut.conj_apply]
    rw [this, Set.image_comp]
    exact (Homeomorph.mulRight x⁻¹).isOpenMap _ ((Homeomorph.mulLeft x).isOpenMap _ hKo)
  have hLc : ∀ x : G, IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    intro x
    have : ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) = (fun g => x * g * x⁻¹) '' (K : Set G) := by
      ext g; simp [MulAut.conj_apply]
    rw [this]
    exact hKc.image (by fun_prop)
  refine ⟨fun x => ⟨inf_le_cptPart' T _ (hLc x), (part _ T Γ C (hLo x) (hLc x) hTc hcomm hΓ hC hcov hfin htor).1⟩,
    fun x => ?_, (part K T Γ C hKo hKc hTc hcomm hΓ hC hcov hfin htor).2,
    finite_doubleCoset K T Γ C hKo hKc hTc hΓ hC hcov⟩
  have : ((Γ ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite := by
    rw [Subgroup.coe_inf]
    exact hfin _ (hLc x)
  exact this.to_subtype

end GlobalTheory.CompanionTheory.CountClosedComm
