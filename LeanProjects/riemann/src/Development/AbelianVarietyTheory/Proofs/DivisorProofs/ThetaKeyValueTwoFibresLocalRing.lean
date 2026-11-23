import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsBaseChangePolarisedDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantsJetsLocalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumPolarisedAbelianLocalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatesIntegralOfLinearlyIndependentReductioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumFibreOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFirstJetsLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarMatrixBetweenKeyDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow

theorem frame_coords_lift {W K₀ K₁ : Type} [CommRing W] [IsDomain W] [Field K₀] [Field K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁)
    (hi₀ : Function.Injective i₀) (hi₁ : ∀ a, i₁ a ≠ 0 → IsUnit a) {I : Type} {g : ℕ} (ϑ ϑ' : I → W)
    (J J' : I → Fin g → W)
    (hind : ∀ (c₀ : K₁) (c : Fin g → K₁), (∀ i, c₀ * i₁ (ϑ' i) + ∑ j, c j * i₁ (J' i j) = 0) → c₀ = 0 ∧ c = 0)
    (a₀ : K₀) (M₀ : Matrix (Fin g) (Fin g) K₀) (c₀ : Fin g → K₀)
    (h0ϑ : ∀ i, i₀ (ϑ i) = a₀ * i₀ (ϑ' i))
    (h0J : ∀ i j, i₀ (J i j) = a₀ * ∑ l, M₀ j l * i₀ (J' i l) + c₀ j * i₀ (ϑ' i))
    (a₁ : K₁) (M₁ : Matrix (Fin g) (Fin g) K₁) (c₁ : Fin g → K₁) (ha₁ : a₁ ≠ 0)
    (h1ϑ : ∀ i, i₁ (ϑ i) = a₁ * i₁ (ϑ' i))
    (h1J : ∀ i j, i₁ (J i j) = a₁ * ∑ l, M₁ j l * i₁ (J' i l) + c₁ j * i₁ (ϑ' i)) :
    ∃ (a : W) (M : Matrix (Fin g) (Fin g) W), i₀ a = a₀ ∧ i₁ a = a₁ ∧ i₀.mapMatrix M = M₀ ∧
      i₁.mapMatrix M = M₁ := by
  let u : I → Option (Fin g) → W := fun i o => Option.elim o (ϑ' i) (J' i)
  have hind' : ∀ c : Option (Fin g) → K₁, (∀ i, ∑ l, c l * i₁ (u i l) = 0) → c = 0 := by
    intro c hc
    obtain ⟨h1, h2⟩ := hind (c none) (fun j => c (some j)) (fun i => by simpa [Fintype.sum_option, u] using hc i)
    funext o
    cases o with
    | none => exact h1
    | some j => exact congrFun h2 j
  obtain ⟨z, hz, hϑz⟩ := GlobalTheory.T.coordinates_integral_of_linearly_independent_reduction W K₀ K₁ i₀ i₁ hi₀ hi₁ I (Option (Fin g)) u hind' ϑ
    (fun o => Option.elim o a₀ 0) (fun i => by simp [Fintype.sum_option, u, h0ϑ])
  have hz0 : ∀ j, z (some j) = 0 := fun j => hi₀ (by simpa using hz (some j))
  have ha₀ : i₀ (z none) = a₀ := by simpa using hz none
  have ha : i₁ (z none) = a₁ := by
    have := hind (i₁ (z none) - a₁) 0 (fun i => by
      have e := congrArg i₁ (hϑz i)
      simp only [Fintype.sum_option, hz0, zero_mul, Finset.sum_const_zero, add_zero, map_mul, h1ϑ, u,
        Option.elim_none] at e
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      linear_combination -e)
    exact sub_eq_zero.1 this.1
  have hN : ∀ j, ∃ N : Option (Fin g) → W, (∀ o, i₀ (N o) = Option.elim o (c₀ j) (fun l => a₀ * M₀ j l)) ∧
      ∀ i, J i j = ∑ o, N o * u i o := by
    intro j
    exact GlobalTheory.T.coordinates_integral_of_linearly_independent_reduction W K₀ K₁ i₀ i₁ hi₀ hi₁ I (Option (Fin g)) u hind' (fun i => J i j) _ (fun i => by
      simp [Fintype.sum_option, u, h0J, Finset.mul_sum, _root_.mul_assoc]; ring)
  choose N hN0 hNJ using hN
  have hN1 : ∀ j l, i₁ (N j (some l)) = a₁ * M₁ j l := by
    intro j
    have := hind (i₁ (N j none) - c₁ j) (fun l => i₁ (N j (some l)) - a₁ * M₁ j l) (fun i => by
      have e := congrArg i₁ (hNJ j i)
      rw [h1J] at e
      simp only [Fintype.sum_option, u, Option.elim_none, Option.elim_some, map_add, map_sum, map_mul, Finset.mul_sum] at e
      simp only [sub_mul, Finset.sum_sub_distrib, _root_.mul_assoc]
      linear_combination -e)
    intro l
    exact sub_eq_zero.1 (congrFun this.2 l)
  obtain ⟨v, hv⟩ := hi₁ (z none) (by rw [ha]; exact ha₁)
  have hne₀ : a₀ ≠ 0 := by rw [← ha₀, ← hv]; exact (v.map i₀.toMonoidHom).ne_zero
  refine ⟨z none, Matrix.of fun j l => ↑v⁻¹ * N j (some l), ha₀, ha, ?_, ?_⟩
  · ext j l
    have h1 : i₀ (↑v⁻¹ : W) = a₀⁻¹ := by
      rw [← ha₀, ← hv]; exact map_units_inv i₀ v
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_mul, h1, Option.elim_some, hN0]
    field_simp
  · ext j l
    have h1 : i₁ (↑v⁻¹ : W) = a₁⁻¹ := by
      rw [← ha, ← hv]; exact map_units_inv i₁ v
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_mul, h1, Option.elim_some, hN1]
    field_simp

theorem thJet_frameChange_castDim {K : Type} [Field K] [CharZero K] (x : KeyIn K) (th : x.P.L.Sec) (hth) (v : Fin x.P.g → (epsR K ⟶ x.P.A)) (hv)
    (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K)
    (hth' : ∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ a * LB.Sec.f th i) (hv' : ∀ i, IsLieComb (M i) v (x.v i))
    {g : ℕ} (hg : x.P.g = g) (m : ℕ) (hm : Odd m) {I : Type} (pt : I → (baseOver (Sp K) ⟶ x.P.A)) (ϑ ϑ' : I → K)
    (J J' : I → Fin g → K)
    (h1 : ThJet ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ hg m pt ϑ J) (h2 : ThJet x hg m pt ϑ' J') :
    (∀ i, ϑ' i = a * ϑ i) ∧ ∃ c : Fin g → K, ∀ i j,
      J' i j = a * ∑ l, M.reindex (finCongr hg) (finCongr hg) j l * J i l + c j * ϑ i := by
  cases x
  subst hg
  have hm0 : (m : K) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; exact (Nat.not_odd_zero hm))
  simpa using GlobalTheory.T.thetaConstants_jets_change_section_basis K _ _ _ _ th hth v hv _ _ _ _ a M hth' hv' m hm hm0 I pt ϑ ϑ' J J' h1 h2

theorem keyValue_twoFibres : ∀ κ : Rule, Rule4 κ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] [IsIntegrallyClosed W] [CharZero W] (K₀ K₁ : Type) [Field K₀] [CharZero K₀] [Field K₁] [IsAlgClosed K₁] [CharZero K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a, i₁ a ≠ 0 → IsUnit a) → ∀ (P : PolAV (Sp W)) (x₀ : KeyIn K₀) (x₁ : KeyIn K₁) (g : ℕ) (h₀ : x₀.P.g = g) (h₁ : x₁.P.g = g) (m : ℕ), P.g = g → Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp W) ⟶ P.A)) (p₀ : I → (baseOver (Sp K₀) ⟶ x₀.P.A)) (p₁ : I → (baseOver (Sp K₁) ⟶ x₁.P.A)) (φ₀ : x₀.P.A.left ⟶ P.A.left) (φ₁ : x₁.P.A.left ⟶ P.A.left), (∀ a, pt a ^ (m ^ 2) = 1) → IsGrpPullback x₀.P.A P.A (spMap i₀) φ₀ → IsGrpPullback x₁.P.A P.A (spMap i₁) φ₁ → LBIso x₀.P.L (P.L.pull φ₀) → LBIso x₁.P.L (P.L.pull φ₁) → (∀ a, (p₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) → (∀ a, (p₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left) → (∀ z : baseOver (Sp K₁) ⟶ x₁.P.A, z ^ (m ^ 2) = 1 → ∃ a, p₁ a = z) → ∀ (ϑ : I → W) (J : I → Fin g → W) (k : W), ThJet x₀ h₀ m p₀ (fun a => i₀ (ϑ a)) (fun a j => i₀ (J a j)) → ThJet x₁ h₁ m p₁ (fun a => i₁ (ϑ a)) (fun a j => i₁ (J a j)) → (κ K₀ x₀ : K₀) = i₀ k → (κ K₁ x₁ : K₁) = i₁ k := by
  intro κ hκ W _ _ _ _ _ _ K₀ K₁ _ _ _ _ _ i₀ i₁ hi₀ hi₁ P x₀ x₁ g h₀ h₁ m hP hm hm3 I pt p₀ p₁ φ₀ φ₁ hpt hpb₀ hpb₁
    hL₀ hL₁ hc₀ hc₁ hsurj ϑ J k hJ₀ hJ₁ hk
  obtain ⟨hHom, -, -, hFam⟩ := hκ
  have hPg : 1 ≤ P.g := hP ▸ h₀ ▸ x₀.g_pos
  obtain ⟨y, rfl⟩ := GlobalTheory.T.exists_keyDatum_polarisedAbelian_localDomain W P hPg
  have hmu : IsUnit (m : W) := hi₁ _ (by rw [map_natCast]; exact_mod_cast (show m ≠ 0 by omega))
  obtain ⟨ϑ', J', hy⟩ := GlobalTheory.T.exists_thetaConstantsJets_localDomain W y g hP m hm hmu I pt hpt
  obtain ⟨th₀, hth₀, v₀, hv₀, hA₀⟩ := GlobalTheory.T.exists_keyDatum_fibre_of_grpPullback W K₀ i₀ y x₀.P φ₀ x₀.g_pos x₀.rig x₀.rig_gen (h₀.trans hP.symm) hpb₀ hL₀
  obtain ⟨th₁, hth₁, v₁, hv₁, hA₁⟩ := GlobalTheory.T.exists_keyDatum_fibre_of_grpPullback W K₁ i₁ y x₁.P φ₁ x₁.g_pos x₁.rig x₁.rig_gen (h₁.trans hP.symm) hpb₁ hL₁
  have hJy₀ := GlobalTheory.T.thetaConstantsJets_baseChange_polarisedDatum W K₀ i₀ y ⟨x₀.P, x₀.g_pos, x₀.rig, x₀.rig_gen, th₀, hth₀, v₀, hv₀⟩ φ₀ hA₀ g hP h₀ m I pt p₀ ϑ' J' hc₀ hy
  have hJy₁ := GlobalTheory.T.thetaConstantsJets_baseChange_polarisedDatum W K₁ i₁ y ⟨x₁.P, x₁.g_pos, x₁.rig, x₁.rig_gen, th₁, hth₁, v₁, hv₁⟩ φ₁ hA₁ g hP h₁ m I pt p₁ ϑ' J' hc₁ hy
  obtain ⟨a₀, M₀, ha₀, hth0, hv0⟩ := GlobalTheory.T.exists_scalar_matrix_between_keyData K₀ x₀.P th₀ x₀.th v₀ x₀.v hth₀ x₀.th_ne hv₀ x₀.basis
  obtain ⟨a₁, M₁, ha₁, hth1, hv1⟩ := GlobalTheory.T.exists_scalar_matrix_between_keyData K₁ x₁.P th₁ x₁.th v₁ x₁.v hth₁ x₁.th_ne hv₁ x₁.basis
  obtain ⟨hu0ϑ, c₀, hu0J⟩ := thJet_frameChange_castDim x₀ th₀ hth₀ v₀ hv₀ a₀ M₀ hth0 hv0 h₀ m hm p₀ _ _ _ _ hJy₀ hJ₀
  obtain ⟨hu1ϑ, c₁, hu1J⟩ := thJet_frameChange_castDim x₁ th₁ hth₁ v₁ hv₁ a₁ M₁ hth1 hv1 h₁ m hm p₁ _ _ _ _ hJy₁ hJ₁
  have hind := GlobalTheory.T.thetaConstants_firstJets_linearIndependent K₁ ⟨x₁.P, x₁.g_pos, x₁.rig, x₁.rig_gen, th₁, hth₁, v₁, hv₁⟩ g h₁ m hm hm3 I p₁ hsurj _ _ hJy₁
  obtain ⟨u, hu⟩ := hFam W y
  have hκy₀ := hu K₀ i₀ ⟨x₀.P, x₀.g_pos, x₀.rig, x₀.rig_gen, th₀, hth₀, v₀, hv₀⟩ ⟨φ₀, hA₀⟩
  have hκy₁ := hu K₁ i₁ ⟨x₁.P, x₁.g_pos, x₁.rig, x₁.rig_gen, th₁, hth₁, v₁, hv₁⟩ ⟨φ₁, hA₁⟩
  have hH₀ := hHom K₀ x₀.P x₀.g_pos x₀.rig x₀.rig_gen th₀ hth₀ v₀ hv₀ x₀.th x₀.th_ne x₀.v x₀.basis a₀ M₀ hth0 hv0
  have hH₁ := hHom K₁ x₁.P x₁.g_pos x₁.rig x₁.rig_gen th₁ hth₁ v₁ hv₁ x₁.th x₁.th_ne x₁.v x₁.basis a₁ M₁ hth1 hv1
  obtain ⟨a, M, ha0, ha1, hM0, hM1⟩ := frame_coords_lift i₀ i₁ hi₀ hi₁ ϑ ϑ' J J' hind a₀ _ c₀ hu0ϑ hu0J a₁ _ c₁ ha₁ hu1ϑ hu1J
  have H₀ : a₀ ^ 8 * (κ K₀ x₀ : K₀) = M₀.det ^ 4 * i₀ u := by rw [← hκy₀]; simpa using hH₀
  have H₁ : a₁ ^ 8 * (κ K₁ x₁ : K₁) = M₁.det ^ 4 * i₁ u := by rw [← hκy₁]; simpa using hH₁
  have e0 : a ^ 8 * k = M.det ^ 4 * u := by
    apply hi₀
    rw [map_mul, map_mul, map_pow, map_pow, ha0, RingHom.map_det, hM0, Matrix.det_reindex_self, ← hk, H₀]
  have e1 := congrArg i₁ e0
  rw [map_mul, map_mul, map_pow, map_pow, ha1, RingHom.map_det, hM1, Matrix.det_reindex_self, ← H₁] at e1
  exact (mul_left_cancel₀ (pow_ne_zero 8 ha₁) e1).symm

end GlobalTheory.MBLow
