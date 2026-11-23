import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagLocallyAdaptedAffineFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentTriangularFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingMinorsUnipotentMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedFlagTriangularFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramesTriangularChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularChangeSpansFlagStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option autoImplicit false
noncomputable section
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.FlagCell.CellOpen

theorem spans_res {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {V W : X.Opens}
    {v : Fin m → Γ(F, V)} (hv : Spans fl V v) (h : W ≤ V) :
    Spans fl W fun j => resM F h (v j) := by
  intro l
  obtain ⟨s, hs, hsv⟩ := hv l
  exact ⟨fun j => resM _ h (s j), hs.res h, fun j => by rw [app_resM, hsv]⟩

theorem res_pullCol {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} {U : B.Opens} {m : ℕ}
    (e : Fin m → Γ(E, U)) {V W : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) (h : W ≤ V)
    (M : Matrix (Fin m) (Fin m) Γ(Y, V)) (j : Fin m) :
    resM _ h (pullCol π e hV M j) = pullCol π e (h.trans hV) (M.map (resG Y h)) j := by
  simp only [pullCol, map_sum, resM_smul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  exact QCoh.res_pullbackSections π E hV h (e l)

theorem sum_smul_pullCol {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} {U : B.Opens} {m : ℕ}
    (e : Fin m → Γ(E, U)) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    (N M : Matrix (Fin m) (Fin m) Γ(Y, V)) (j : Fin m) :
    ∑ k, M k j • pullCol π e hV N k = pullCol π e hV (N * M) j := by
  simp only [pullCol, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem isFrame_pullbackSections {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} [E.IsQuasicoherent]
    {U : B.Opens} {m : ℕ} {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) :
    IsFrame fun l => QCoh.pullbackSections π E hV (e l) := by
  have := (he.pullback π).res hV
  rwa [funext fun i => QCoh.res_pullbackSections π E le_rfl hV (e i)] at this

theorem exists_pullCol {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} [E.IsQuasicoherent]
    {U : B.Opens} {m : ℕ} {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    (v : Fin m → Γ((Scheme.Modules.pullback π).obj E, V)) :
    ∃ M : Matrix (Fin m) (Fin m) Γ(Y, V), ∀ j, v j = pullCol π e hV M j := by
  have hb := isFrame_pullbackSections π he hV V le_rfl
  choose c hc using fun j => hb.2 (v j)
  refine ⟨Matrix.of fun l j => c j l, fun j => ?_⟩
  rw [← hc j, Fintype.linearCombination_apply]
  simp only [pullCol, Matrix.of_apply, resM_self]

theorem pullCol_injective {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} [E.IsQuasicoherent]
    {U : B.Opens} {m : ℕ} {e : Fin m → Γ(E, U)} (he : IsFrame e) {V : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U)
    {M N : Matrix (Fin m) (Fin m) Γ(Y, V)} (h : ∀ j, pullCol π e hV M j = pullCol π e hV N j) :
    M = N := by
  have hb := isFrame_pullbackSections π he hV V le_rfl
  ext l j
  have := hb.1 (a₁ := fun l => M l j) (a₂ := fun l => N l j) (by
    simp only [Fintype.linearCombination_apply, resM_self]
    exact h j)
  exact congrFun this l

theorem isUnit_minor_of_upper {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (hM : M.BlockTriangular id) (hd : IsUnit M.det) (l : Fin (m + 1)) :
    IsUnit (M.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
  have hM' : (M.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).BlockTriangular id :=
    fun i j hij => hM (show Fin.castLE l.is_le j < Fin.castLE l.is_le i from hij)
  rw [Matrix.det_of_isUpperTriangular hM']
  rw [Matrix.det_of_isUpperTriangular hM] at hd
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => ?_
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun k => M k k) (Finset.mem_univ _)) hd

theorem mem_basicOpen_of_isUnit_appLE {T Y : Scheme.{0}} (g' : T ⟶ Y) {V : Y.Opens} {V' : T.Opens}
    (h : V' ≤ g' ⁻¹ᵁ V) (d : Γ(Y, V)) (hd : IsUnit (g'.appLE V V' h d)) {t : T} (ht : t ∈ V') :
    g' t ∈ Y.basicOpen d := by
  have e := Scheme.basicOpen_appLE g' V' V h d
  rw [T.basicOpen_of_isUnit hd] at e
  have : t ∈ V' ⊓ g' ⁻¹ᵁ Y.basicOpen d := e ▸ ht
  exact this.2

theorem isUnit_resG_of_le_basicOpen {Y : Scheme.{0}} {V W : Y.Opens} (d : Γ(Y, V))
    (h : W ≤ Y.basicOpen d) : IsUnit (resG Y (h.trans (Y.basicOpen_le d)) d) := by
  have hu : IsUnit (resG Y (Y.basicOpen_le d) d) := RingedSpace.isUnit_res_basicOpen _ d
  have := hu.map (resG Y h)
  rwa [resG_resG] at this

end GlobalTheory.FlagCell.CellOpen

namespace GlobalTheory.FlagCell.CellOpen

theorem mem_finset_inf {X : Scheme.{0}} {κ : Type} [Fintype κ] (W : κ → X.Opens) (x : X)
    (h : ∀ k, x ∈ W k) : x ∈ Finset.univ.inf W := by
  rw [← SetLike.mem_coe, Opens.coe_finset_inf]
  simpa using h

theorem spans_uniR_near_image : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens) (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∀ (T : Scheme.{0}) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)), Carries π E r fl g' g w fl' → ∀ (V' : T.Opens) (hV' : V' ≤ g ⁻¹ᵁ U) (n' : (Σ a, Low (r a)) → Γ(T, V')), (∀ a, Spans (fl' a) V' (pullCol g (eU a) hV' (uniR fun s => n' ⟨a, s⟩))) → ∀ t ∈ V', ∃ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, V)), g' t ∈ V ∧ ∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n ⟨a, s⟩)) := by
  intro B Y π ι _ r E fl hE U eU heU T g' g w fl' hC V' hV' n' hn' t ht
  haveI : ∀ a, (E a).IsQuasicoherent := fun a => (hE a).isQuasicoherent
  have hy : ∀ a, ∃ W : Y.Opens, g' t ∈ W ∧ ∃ v : Fin (r a) → Γ((Scheme.Modules.pullback π).obj (E a), W),
      Spans (fl a) W v := by
    intro a
    obtain ⟨W, hW, u, -, hs⟩ := GlobalTheory.FlagZ.Loc.exists_nested_frames (fl a) (g' t) (Fin.last (r a))
    exact ⟨W, hW, fun j => ((fl a).ι (Fin.last _)).app W (u j), fun l => hs l l.is_le⟩
  choose W hyW v hv using hy
  have hπ : g' t ∈ π ⁻¹ᵁ U := by
    have h1 := hV' ht
    rw [← w] at h1
    exact h1
  let V₀ : Y.Opens := π ⁻¹ᵁ U ⊓ Finset.univ.inf W
  have hyV₀ : g' t ∈ V₀ := ⟨hπ, mem_finset_inf W _ hyW⟩
  have hV₀a : ∀ a, V₀ ≤ W a := fun a => inf_le_right.trans (Finset.inf_le (Finset.mem_univ a))
  have hV₀U : V₀ ≤ π ⁻¹ᵁ U := inf_le_left
  have hA : ∀ a, ∃ A : Matrix (Fin (r a)) (Fin (r a)) Γ(Y, V₀),
      Spans (fl a) V₀ (pullCol π (eU a) hV₀U A) := by
    intro a
    obtain ⟨A, hA⟩ := exists_pullCol π (heU a) hV₀U (fun j => resM _ (hV₀a a) (v a j))
    refine ⟨A, ?_⟩
    have := spans_res (hv a) (hV₀a a)
    convert this using 1
    funext j
    exact (hA j).symm
  choose A hA using hA
  let V'' : T.Opens := V' ⊓ g' ⁻¹ᵁ V₀
  have htV'' : t ∈ V'' := ⟨ht, hyV₀⟩
  have h₁ : V'' ≤ g' ⁻¹ᵁ V₀ := inf_le_right
  have h₂ : V'' ≤ g ⁻¹ᵁ U := inf_le_left.trans hV'
  have hmin : ∀ a (l : Fin (r a + 1)),
      IsUnit ((g'.appLE V₀ V'' h₁).hom ((A a).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det) := by
    intro a l
    have hp := GlobalTheory.T.carried_flag_triangular_frame B Y T π ι r E fl g' g w fl' hC U a (eU a) V₀ hV₀U (A a) V'' h₁ h₂ (hA a)
    have hq : Spans (fl' a) V'' (pullCol g (eU a) h₂
        (uniR fun s => resG T (inf_le_left : V'' ≤ V') (n' ⟨a, s⟩))) := by
      have := spans_res (hn' a) (inf_le_left : V'' ≤ V')
      convert this using 1
      funext j
      rw [res_pullCol, map_uniR]
    obtain ⟨M, hMt, hMd, hM⟩ := GlobalTheory.T.flag_frames_triangular_change T _ (r a) (fl' a) V'' _ _ hq hp
    have heq : (A a).map (g'.appLE V₀ V'' h₁).hom =
        (uniR fun s => resG T (inf_le_left : V'' ≤ V') (n' ⟨a, s⟩)) * M := by
      apply pullCol_injective g (heU a) h₂
      intro j
      rw [hM j, sum_smul_pullCol]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, heq,
      GlobalTheory.T.leading_minors_unipotent_mul _ (r a) _ M hMt l]
    exact isUnit_minor_of_upper M hMt hMd l
  let D : (Σ a, Fin (r a + 1)) → Y.Opens := fun p =>
    Y.basicOpen ((A p.1).submatrix (Fin.castLE p.2.is_le) (Fin.castLE p.2.is_le)).det
  let V₁ : Y.Opens := V₀ ⊓ Finset.univ.inf D
  have hyV₁ : g' t ∈ V₁ :=
    ⟨hyV₀, mem_finset_inf D _ fun p => mem_basicOpen_of_isUnit_appLE g' h₁ _ (hmin p.1 p.2) htV''⟩
  have hV₁₀ : V₁ ≤ V₀ := inf_le_left
  have hV₁U : V₁ ≤ π ⁻¹ᵁ U := hV₁₀.trans hV₀U
  have hLU : ∀ a, ∃ n : Low (r a) → Γ(Y, V₁), Spans (fl a) V₁ (pullCol π (eU a) hV₁U (uniR n)) := by
    intro a
    have hunit : ∀ l : Fin (r a + 1),
        IsUnit (((A a).map (resG Y hV₁₀)).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
      intro l
      rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      have hle : V₁ ≤ D ⟨a, l⟩ := inf_le_right.trans (Finset.inf_le (Finset.mem_univ _))
      exact isUnit_resG_of_le_basicOpen _ hle
    obtain ⟨n, M₁, hM₁t, hM₁d, hM₁⟩ := GlobalTheory.T.exists_unipotent_triangular_factor _ (r a) _ hunit
    refine ⟨n, ?_⟩
    have hs' : Spans (fl a) V₁ (pullCol π (eU a) hV₁U (uniR n * M₁)) := by
      have hs := spans_res (hA a) hV₁₀
      convert hs using 1
      funext j
      rw [res_pullCol, hM₁]
    haveI := M₁.invertibleOfIsUnitDet hM₁d
    have := GlobalTheory.T.triangular_change_spans_flag Y _ (r a) (fl a) V₁ _ M₁⁻¹ hs'
      (Matrix.blockTriangular_inv_of_blockTriangular hM₁t) (Matrix.isUnit_nonsing_inv_det _ hM₁d)
    convert this using 1
    funext j
    rw [sum_smul_pullCol, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM₁d, Matrix.mul_one]
  choose n hn using hLU
  exact ⟨V₁, hV₁U, fun p => n p.1 p.2, hyV₁, fun a => hn a⟩

end GlobalTheory.FlagCell.CellOpen
