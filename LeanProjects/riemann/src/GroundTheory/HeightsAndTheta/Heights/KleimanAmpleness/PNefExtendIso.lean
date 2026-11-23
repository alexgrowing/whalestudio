import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefExtendIsoSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExtendTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

namespace NefExtendIso

variable {S : Type} [CommRing S] {F : Type} [Field F] [Algebra S F] {Ω : Type} [Field Ω] [Algebra S Ω]
  [Algebra F Ω] [IsScalarTower S F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem map_mem_monos_hom {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R')
    {I : Finset (Fin (N + 1))} {s : Kleiman.Poly R N} (hs : s ∈ Kleiman.monos I) :
    map g s ∈ Kleiman.monos (S := R') I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]
    exact Submonoid.subset_closure ⟨i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem map_homogeneousComponent {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ)
    (f : Kleiman.Poly R N) : map g (homogeneousComponent d f) = homogeneousComponent d (map g f) := by
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

theorem map_pre (hφ : Function.Bijective (algebraMap S F)) (f : Kleiman.Poly F N) :
    map (algebraMap S F) (map ((RingEquiv.ofBijective _ hφ).symm : F →+* S) f) = f := by
  have hc : (algebraMap S F).comp ((RingEquiv.ofBijective _ hφ).symm : F →+* S) = RingHom.id F :=
    RingHom.ext fun y => (RingEquiv.ofBijective _ hφ).apply_symm_apply y
  rw [map_map, hc, map_id]

theorem mem_chartRing_iff (hφ : Function.Bijective (algebraMap S F)) {I : Kleiman.Chart x} {a : Ω} :
    a ∈ Kleiman.chartRing F x I ↔ a ∈ Kleiman.chartRing S x I := by
  constructor
  · rintro ⟨f, s, e, hs, hf, hse, rfl⟩
    let g : F →+* S := (RingEquiv.ofBijective _ hφ).symm
    refine ⟨map g f, map g s, e, map_mem_monos_hom g hs, hf.map g, hse.map g, ?_⟩
    rw [← aeval_map_algebraMap F x (map g f), ← aeval_map_algebraMap F x (map g s), map_pre hφ,
      map_pre hφ]
  · exact Kleiman.mem_chartRing_extend

theorem span_coe_submodule (hφ : Function.Bijective (algebraMap S F)) (I : Kleiman.Chart x)
    (M : Submodule (Kleiman.chartRing S x I) Ω) :
    ((Submodule.span (Kleiman.chartRing F x I) (M : Set Ω) : Submodule _ Ω) : Set Ω) = M := by
  apply le_antisymm
  · intro z hz
    refine Submodule.span_induction (p := fun z _ => z ∈ M) (fun y hy => hy) M.zero_mem
      (fun _ _ _ _ ha hb => M.add_mem ha hb) ?_ hz
    intro a z _ hz
    have : a • z = (⟨(a : Ω), (mem_chartRing_iff hφ).mp a.2⟩ : Kleiman.chartRing S x I) • z := by
      rw [Kleiman.chartRing_smul_def, Kleiman.chartRing_smul_def]
    rw [this]
    exact M.smul_mem _ hz
  · exact Submodule.subset_span

theorem span_same (hφ : Function.Bijective (algebraMap S F)) (I : Kleiman.Chart x) (P : Set Ω) :
    ((Submodule.span (Kleiman.chartRing S x I) P : Submodule _ Ω) : Set Ω) =
      (Submodule.span (Kleiman.chartRing F x I) P : Submodule _ Ω) := by
  rw [← Kleiman.span_extend_span (S := S) (F := F) I P, span_coe_submodule hφ]

def Same (A : Kleiman.SubSystem S x Ω) (B : Kleiman.SubSystem F x Ω) : Prop :=
  ∀ I, (A.sub I : Set Ω) = B.sub I

theorem same_extend (hφ : Function.Bijective (algebraMap S F)) (Q : Kleiman.SubSystem S x Ω) :
    Same Q (Q.extend F) := fun I => (span_coe_submodule hφ I (Q.sub I)).symm

theorem same_twist (hφ : Function.Bijective (algebraMap S F)) {A A' : Kleiman.SubSystem S x Ω}
    {B B' : Kleiman.SubSystem F x Ω} (h : Same A B) (h' : Same A' B') :
    Same (A.twist A') (B.twist B') := by
  intro I
  have hX : {z : Ω | ∃ q ∈ A'.sub I, ∃ y ∈ A.sub I, z = q • y} =
      {z : Ω | ∃ q ∈ B'.sub I, ∃ y ∈ B.sub I, z = q • y} := by
    ext z
    constructor
    · rintro ⟨q, hq, y, hy, rfl⟩
      exact ⟨q, (Set.ext_iff.mp (h' I) q).mp hq, y, (Set.ext_iff.mp (h I) y).mp hy, rfl⟩
    · rintro ⟨q, hq, y, hy, rfl⟩
      exact ⟨q, (Set.ext_iff.mp (h' I) q).mpr hq, y, (Set.ext_iff.mp (h I) y).mpr hy, rfl⟩
  change ((Submodule.span (Kleiman.chartRing S x I) {z : Ω | ∃ q ∈ A'.sub I, ∃ y ∈ A.sub I, z = q • y} :
      Submodule _ Ω) : Set Ω) =
    (Submodule.span (Kleiman.chartRing F x I) {z : Ω | ∃ q ∈ B'.sub I, ∃ y ∈ B.sub I, z = q • y} :
      Submodule _ Ω)
  rw [← hX, span_same hφ]

theorem same_twistSys (hφ : Function.Bijective (algebraMap S F)) (c : ℤ) :
    Same (Kleiman.twistSys S x c) (Kleiman.twistSys F x c) := by
  have := same_extend hφ (Kleiman.twistSys S x c)
  rwa [Kleiman.SubSystem.extend_twistSys] at this

theorem same_tensorSub (hφ : Function.Bijective (algebraMap S F)) {n : ℕ}
    {L : Fin n → Kleiman.SubSystem S x Ω} {L' : Fin n → Kleiman.SubSystem F x Ω}
    (hL : ∀ i, Same (L i) (L' i)) (T : Finset (Fin n)) :
    Same (Kleiman.tensorSub L T) (Kleiman.tensorSub L' T) := by
  have key : ∀ (l : List (Fin n)) (A : Kleiman.SubSystem S x Ω) (B : Kleiman.SubSystem F x Ω),
      Same A B → Same (l.foldl (fun G i => G.twist (L i)) A) (l.foldl (fun G i => G.twist (L' i)) B) := by
    intro l
    induction l with
    | nil => intro A B h; exact h
    | cons i l ih => intro A B h; exact ih _ _ (same_twist hφ h (hL i))
  exact key _ _ _ (same_twistSys hφ 0)

theorem same_idealSys (hφ : Function.Bijective (algebraMap S F)) (p' : Ideal (Kleiman.Poly F N)) :
    Same (Kleiman.idealSys x (p'.comap (map (algebraMap S F)))) (Kleiman.idealSys x p') := by
  intro I
  let g : F →+* S := (RingEquiv.ofBijective _ hφ).symm
  have hG : {a : Ω | ∃ (f s : Kleiman.Poly S N) (e : ℕ), f ∈ p'.comap (map (algebraMap S F)) ∧
      s ∈ Kleiman.monos I.1 ∧ f.IsHomogeneous e ∧ s.IsHomogeneous e ∧ a = aeval x f / aeval x s} =
      {a : Ω | ∃ (f s : Kleiman.Poly F N) (e : ℕ), f ∈ p' ∧ s ∈ Kleiman.monos I.1 ∧ f.IsHomogeneous e ∧
        s.IsHomogeneous e ∧ a = aeval x f / aeval x s} := by
    ext a
    constructor
    · rintro ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
      exact ⟨map (algebraMap S F) f, map (algebraMap S F) s, e, Ideal.mem_comap.mp hf,
        map_mem_monos_hom _ hs, hfe.map _, hse.map _, by
          rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩
    · rintro ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
      refine ⟨map g f, map g s, e, Ideal.mem_comap.mpr (by rwa [map_pre hφ]),
        map_mem_monos_hom g hs, hfe.map g, hse.map g, ?_⟩
      rw [← aeval_map_algebraMap F x (map g f), ← aeval_map_algebraMap F x (map g s), map_pre hφ,
        map_pre hφ]
  change ((Submodule.span (Kleiman.chartRing S x I) _ : Submodule _ Ω) : Set Ω) =
    (Submodule.span (Kleiman.chartRing F x I) _ : Submodule _ Ω)
  rw [hG, span_same hφ]

omit [Algebra S F] [IsScalarTower S F Ω] in

theorem same_secs {A : Kleiman.SubSystem S x Ω} {B : Kleiman.SubSystem F x Ω} (h : Same A B) :
    (A.secs : Set Ω) = B.secs := by
  ext z
  simp only [SetLike.mem_coe, Kleiman.SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  exact forall_congr' fun I => Set.ext_iff.mp (h I) z

theorem length_quot_eq (hφ : Function.Bijective (algebraMap S F)) (X Y : Submodule S Ω)
    (X' Y' : Submodule F Ω) (hX : (X : Set Ω) = X') (hY : (Y : Set Ω) = Y') :
    Module.length S (X ⧸ Y.comap X.subtype) = Module.length F (X' ⧸ Y'.comap X'.subtype) := by
  obtain rfl : X = X'.restrictScalars S := SetLike.coe_injective hX
  obtain rfl : Y = Y'.restrictScalars S := SetLike.coe_injective hY
  rw [← Module.length_eq_of_surjective (S := S) hφ.2]
  exact (Submodule.Quotient.restrictScalarsEquiv S (Y'.comap X'.subtype)).length_eq

theorem restrLen_eq (hφ : Function.Bijective (algebraMap S F)) {p : Ideal (Kleiman.Poly S N)}
    {p' : Ideal (Kleiman.Poly F N)} (hp : Same (Kleiman.idealSys x p) (Kleiman.idealSys x p'))
    {A : Kleiman.SubSystem S x Ω} {B : Kleiman.SubSystem F x Ω} (h : Same A B) :
    Kleiman.restrLen p A = Kleiman.restrLen p' B := by
  unfold Kleiman.restrLen
  rw [length_quot_eq hφ _ _ _ _ (same_secs h) (same_secs (same_twist hφ h hp))]

theorem interNum_extend (hφ : Function.Bijective (algebraMap S F)) (Q : Kleiman.SubSystem S x Ω)
    (p' : Ideal (Kleiman.Poly F N)) :
    Kleiman.interNum p' ![Q.extend F] = Kleiman.interNum (p'.comap (map (algebraMap S F))) ![Q] := by
  have hL : ∀ i, Same (![Q] i) (![Q.extend F] i) := Fin.forall_fin_one.mpr (same_extend hφ Q)
  unfold Kleiman.interNum
  congr 1
  funext c
  unfold Kleiman.interSum
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [restrLen_eq hφ (same_idealSys hφ p')
    (same_twist hφ (same_tensorSub hφ hL T) (same_twistSys hφ (c : ℤ)))]

theorem isSubvar_comap (hφ : Function.Bijective (algebraMap S F)) {p' : Ideal (Kleiman.Poly F N)} {e : ℕ}
    (hp' : Kleiman.IsSubvar x p' e) : Kleiman.IsSubvar x (p'.comap (map (algebraMap S F))) e where
  isPrime := by have := hp'.isPrime; exact Ideal.comap_isPrime _ _
  homog f hf d := by
    rw [Ideal.mem_comap, map_homogeneousComponent]
    exact hp'.homog _ hf d
  le f hf := by
    rw [Kleiman.primeOf_eq, RingHom.mem_ker, Kleiman.cone_eq, Kleiman.coneGen] at hf
    apply hp'.le
    rw [Kleiman.primeOf_eq, RingHom.mem_ker, Kleiman.cone_eq, Kleiman.coneGen, aeval_map_algebraMap]
    exact hf
  relevant := by
    obtain ⟨i, hi⟩ := hp'.relevant
    exact ⟨i, fun h => hi (by rwa [Ideal.mem_comap, map_X] at h)⟩
  dim := by
    let e' : Kleiman.Poly S N ≃+* Kleiman.Poly F N := mapEquiv _ (RingEquiv.ofBijective _ hφ)
    have he : (e' : Kleiman.Poly S N →+* Kleiman.Poly F N) = map (algebraMap S F) := RingHom.ext fun _ => rfl
    refine (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ p' e' ?_)).trans hp'.dim
    rw [he, Ideal.map_comap_of_surjective _ (fun f => ⟨_, map_pre hφ f⟩)]

end NefExtendIso

theorem NefExtendIso.proof : NefExtendIso.Statement := by
  intro S _ F _ _ Ω _ _ _ _ N x Q hφ hQ p' _ hp'
  rw [NefExtendIso.interNum_extend hφ Q p']
  exact hQ _ bot_le (NefExtendIso.isSubvar_comap hφ hp')

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
