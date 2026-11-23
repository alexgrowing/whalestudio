import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DAmitsur
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Mathlib.Topology.Algebra.ClopenNhdofOne

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem lc_nhds {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {f : G → X} (hf : IsLocallyConstant f) : ∀ᶠ h in nhds (1 : G), ∀ g, f (g * h) = f g := by
  have h1 : ∀ y ∈ Set.range f, ∀ᶠ h in nhds (1 : G), ∀ g, f g = y → f (g * h) = y := by
    intro y _
    obtain ⟨T, hT, hW⟩ := IsTopologicalGroup.exist_mul_closure_nhds (hf.isClopen_fiber y)
    filter_upwards [hT] with h hh g hg
    exact hW (Set.mul_mem_mul (show g ∈ {x | f x = y} from hg) hh)
  filter_upwards [(Filter.eventually_all_finite hf.range_finite).2 h1] with h hh g
  exact hh _ ⟨g, rfl⟩ g rfl

private theorem lift_single {A G ι : Type} [CommRing A] [Group G] (g : ι → G) (w : FreeMonoid ι) :
    FreeMonoid.lift (fun a => (MonoidAlgebra.single (g a) 1 : MonoidAlgebra A G)) w =
      MonoidAlgebra.single (FreeMonoid.lift g w) 1 := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [MonoidAlgebra.one_def]
  | of_mul a w ih => simp [ih, MonoidAlgebra.single_mul_single]

private theorem lift_mk {G ι : Type} [Group G] (H : Subgroup G) [H.Normal] (g g' : ι → G)
    (hg : ∀ a, (g a : G ⧸ H) = g' a) (w : FreeMonoid ι) :
    ((FreeMonoid.lift g w : G) : G ⧸ H) = (FreeMonoid.lift g' w : G) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih => simp [ih, hg]

private theorem key_fin {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (H : Subgroup G) [H.Normal]
    (hD : ∀ i ≤ n, ∀ h ∈ H, ∀ g, D.lam i (MonoidAlgebra.single (g * h) 1) = D.lam i (MonoidAlgebra.single g 1))
    {k : ℕ} (g g' : Fin k → G) (hg : ∀ a, (g a : G ⧸ H) = g' a) (S : Type) [CommRing S] [Algebra A S]
    (s : Fin k → S) :
    D.D S (1 + ∑ a, MonoidAlgebra.single (g a) (s a)) = D.D S (1 + ∑ a, MonoidAlgebra.single (g' a) (s a)) := by
  have h1 : ∀ g : Fin k → G, D.D S (1 + ∑ a, MonoidAlgebra.single (g a) (s a)) =
      MvPolynomial.aeval s (D.toDet.D (MvPolynomial (Fin k) A)
        (1 + Det.gen fun a => (MonoidAlgebra.single (g a) 1 : MonoidAlgebra A G))) := by
    intro g
    rw [← D.toDet.nat]
    change _ = D.D S (ofT A G S _)
    congr 1
    simp [Det.gen, map_sum, ofT_tmul]
  rw [h1, h1]
  congr 1
  ext α
  obtain ⟨P, hP, -, hP'⟩ := d_amitsur n k α
  rw [hP', hP']
  refine MvPolynomial.hom_congr_vars ?_ ?_ rfl
  · ext a
    simp
  · intro v hv _
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, lift_single, (d_toDet D _).2.1]
    have h2 := QuotientGroup.eq.1 (lift_mk H g g' hg v.2)
    rw [← hD v.1 (hP v hv).2.1 _ h2, mul_inv_cancel_left]

private theorem key {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (H : Subgroup G) [H.Normal]
    (hD : ∀ i ≤ n, ∀ h ∈ H, ∀ g, D.lam i (MonoidAlgebra.single (g * h) 1) = D.lam i (MonoidAlgebra.single g 1))
    {ι : Type} [Fintype ι] (g g' : ι → G) (hg : ∀ a, (g a : G ⧸ H) = g' a) (S : Type) [CommRing S] [Algebra A S]
    (s : ι → S) :
    D.D S (1 + ∑ a, MonoidAlgebra.single (g a) (s a)) = D.D S (1 + ∑ a, MonoidAlgebra.single (g' a) (s a)) := by
  let e := (Fintype.equivFin ι).symm
  rw [← e.sum_comp, ← e.sum_comp (fun a => MonoidAlgebra.single (g' a) (s a))]
  exact key_fin D H hD (g ∘ e) (g' ∘ e) (fun a => hg _) S (s ∘ e)

private theorem kills {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (H : Subgroup G) [H.Normal]
    (hD : ∀ i ≤ n, ∀ h ∈ H, ∀ g, D.lam i (MonoidAlgebra.single (g * h) 1) = D.lam i (MonoidAlgebra.single g 1))
    {h : G} (hh : h ∈ H) : D.Kills (MonoidAlgebra.single h 1 - 1) := by
  intro S _ _ u
  have hu : ∃ (ι : Type) (_ : Fintype ι) (g : ι → G) (s : ι → S), u = ∑ a, MonoidAlgebra.single (g a) (s a) := by
    induction u using MonoidAlgebra.induction_linear with
    | zero => exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, by simp⟩
    | single g r => exact ⟨Unit, inferInstance, fun _ => g, fun _ => r, by simp⟩
    | add a b ha hb =>
      obtain ⟨ι, _, g, s, rfl⟩ := ha
      obtain ⟨ι', _, g', s', rfl⟩ := hb
      exact ⟨ι ⊕ ι', inferInstance, Sum.elim g g', Sum.elim s s', by simp⟩
  obtain ⟨ι, _, g, s, rfl⟩ := hu
  have h1 := key D H hD (ι := ι ⊕ ι) (Sum.elim (fun a => g a * h) g) (Sum.elim g g)
    (by rintro (a | a)
        · simpa using hh
        · rfl) S (Sum.elim s fun a => - s a)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, MonoidAlgebra.single_neg, Finset.sum_neg_distrib,
    add_neg_cancel, add_zero, map_one] at h1
  rw [← h1]
  congr 2
  simp [mul_sub, Finset.sum_mul, MonoidAlgebra.single_mul_single, sub_eq_add_neg, mul_add]

theorem UpperTheory.V.CA.exists_openNormalSubgroup_kills_of_groupDetLaw_isCont :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (I : Ideal A), D.IsCont I → ∀ N : ℕ, ∃ H : OpenNormalSubgroup G, ∀ h ∈ H, (D.map (Ideal.Quotient.mk (I ^ N))).Kills (MonoidAlgebra.single h 1 - 1) := by
  intro n A G _ _ D _ _ _ _ I hD N
  have h1 := (Filter.eventually_all_finite (Set.finite_Iic n)).2 fun i _ => lc_nhds (hD i N)
  obtain ⟨U, hU, hUo, hU1⟩ := mem_nhds_iff.1 h1
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo hU1
  refine ⟨H, fun h hh => kills _ H.toSubgroup ?_ hh⟩
  intro i hi h hh g
  have h2 : ∀ g : G, (D.map (Ideal.Quotient.mk (I ^ N))).lam i (MonoidAlgebra.single g 1) =
      Ideal.Quotient.mk (I ^ N) (D.lam i (MonoidAlgebra.single g 1)) := by
    intro g
    rw [← ((d_gmap D).2.2.1 _ _).2 i, MonoidAlgebra.mapRingHom_single, map_one]
  rw [h2, h2]
  exact hU (hH hh) i hi g
