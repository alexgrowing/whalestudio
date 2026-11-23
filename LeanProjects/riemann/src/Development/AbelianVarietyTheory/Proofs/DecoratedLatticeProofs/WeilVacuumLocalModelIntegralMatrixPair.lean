import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSelfDualLatticeSplitPlaceDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexIntegralMatricesInSubstitutionImageStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocOm

theorem indicator_mem_sb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (a : GL Y' k) (b : GL Y k) (v : Matrix Y Y' k), ({x : Matrix Y Y' k | ∀ r q, ((b : Matrix Y Y k) * (x + v) * (a : Matrix Y' Y' k)) r q ∈ 𝒪[k]}).indicator (fun _ => (1 : ℂ)) ∈ SB (Matrix Y Y' k) := by
  intro k _ _ _ _ Y Y' _ _ _ _ a b v
  classical
  have hO : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have hK : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hC : IsClosed (𝒪[k] : Set k) := AddSubgroup.isClosed_of_isOpen (𝒪[k].toAddSubgroup) hO
  let M : Set (Matrix Y Y' k) := {A | ∀ i j, A i j ∈ 𝒪[k]}
  have hMeq : M = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    ext A; exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  have hMK : IsCompact M := by rw [hMeq]; exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  have hMO : IsOpen M := by
    have : M = ⋂ i, ⋂ j, (fun A : Matrix Y Y' k => A i j) ⁻¹' (𝒪[k] : Set k) := by ext A; simp [M]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (continuous_id.matrix_elem i j)
  have hMC : IsClosed M := by
    have : M = ⋂ i, ⋂ j, (fun A : Matrix Y Y' k => A i j) ⁻¹' (𝒪[k] : Set k) := by ext A; simp [M]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j => hC.preimage (continuous_id.matrix_elem i j)
  let φ : Matrix Y Y' k → Matrix Y Y' k := fun x => (b : Matrix Y Y k) * (x + v) * (a : Matrix Y' Y' k)
  let χ : Matrix Y Y' k → Matrix Y Y' k := fun A => ((b⁻¹ : GL Y k) : Matrix Y Y k) * A * ((a⁻¹ : GL Y' k) : Matrix Y' Y' k) - v
  have hφ : Continuous φ := (continuous_const.matrix_mul (continuous_id.add continuous_const)).matrix_mul continuous_const
  have hχ : Continuous χ := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).sub continuous_const
  have hχφ : ∀ x, χ (φ x) = x := fun x => by
    show ((b⁻¹ : GL Y k) : Matrix Y Y k) * ((b : Matrix Y Y k) * (x + v) * (a : Matrix Y' Y' k)) * ((a⁻¹ : GL Y' k) : Matrix Y' Y' k) - v = x
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
      Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, add_sub_cancel_right]
  let U : Set (Matrix Y Y' k) := {x | ∀ r q, ((b : Matrix Y Y k) * (x + v) * (a : Matrix Y' Y' k)) r q ∈ 𝒪[k]}
  have hU : U = φ ⁻¹' M := rfl
  have hUK : IsCompact U := by
    have : U = χ '' M := by
      ext x; constructor
      · intro hx; exact ⟨φ x, hx, hχφ x⟩
      · rintro ⟨A, hA, rfl⟩
        change φ (χ A) ∈ M
        have : φ (χ A) = A := by
          show (b : Matrix Y Y k) * ((((b⁻¹ : GL Y k) : Matrix Y Y k) * A * ((a⁻¹ : GL Y' k) : Matrix Y' Y' k) - v) + v) * (a : Matrix Y' Y' k) = A
          rw [sub_add_cancel, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        rw [this]; exact hA
    rw [this]; exact hMK.image hχ
  have hcl : IsClopen U := ⟨hMC.preimage hφ, hMO.preimage hφ⟩
  refine ⟨?_, HasCompactSupport.intro hUK fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.charFn ℂ hcl).isLocallyConstant

open GlobalTheory.SplitScalar GlobalTheory.SplitHecke in
theorem om_sum_scale_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f → f ≠ 0 → ∀ (c : ℂ), ‖c‖ = 1 → ∀ (r : ℝ), 0 < r → ∀ (R : Finset (WO S T)), (∀ u ∈ R, ∀ u' ∈ R, u ≠ u' → ∃ (l : WO S T) (ε : ℂ), ‖ε‖ = 1 ∧ heisO ψ S T l f = ε • f ∧ ψ (symplO S T (u - u') l) ≠ 1) → ω (g, h) f = ((r : ℂ) * c) • ∑ u ∈ R, heisO ψ S T u f → r = (Real.sqrt (R.card : ℝ))⁻¹ := by
  intro D ψ S T χS χT ω hW g h f hf hf0 c hc r hr R hpair hom
  have hψ := hW.std.1
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ⟩, c', hc'⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hKc f hf.cont hf0
    (by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul]))
  have hn : nrm2 μ 𝓕 (c' • f) = 1 := hc' μ 𝓕 hμ.1 hμ.2.1 hμ.2.2
  have hcf := GlobalTheory.WeilVacMove.isTheta_smul c' hf
  have h1 : ω (g, h) (c' • f) = ((r : ℂ) * c) • ∑ u ∈ R, heisO ψ S T u (c' • f) := by
    rw [map_smul, hom, smul_comm, Finset.smul_sum]
    simp only [heisO_smul]
  have h2 : nrm2 μ 𝓕 (ω (g, h) (c' • f)) = 1 := by
    rw [← hn, nrm2, nrm2, integral_normSq_eq _ (hW.om_pres _ _ hcf).cont.measurable,
      integral_normSq_eq _ hcf.cont.measurable, hW.om_unit μ 𝓕 hμ.1 hμ.2.1 _ _ hcf]
  have h3 := GlobalTheory.HeisOrtho.thetaNormSq_sum_heisenbergTranslates_distinctChars D ψ S T hψ μ 𝓕 hμ _ hcf hn _ R (fun u => u)
    (fun _ => c) (fun _ _ => hc) (fun u hu u' hu' hne => by
      obtain ⟨l, ε, hε, hl, hne'⟩ := hpair u hu u' hu' hne
      exact ⟨l, ε, hε, by rw [heisO_smul, hl, smul_comm], hne'⟩)
  rw [h1, mul_smul, pairNorm_smul, Finset.smul_sum, h3] at h2
  rw [← Real.sqrt_inv, ← eq_inv_of_mul_eq_one_left h2, Real.sqrt_sq hr.le]

theorem exists_detAt_loc : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z) (g : GA D V) (gk : GL Z k), p.IsLoc F g gk → ∃ x : (AE D)ˣ, IsDetAt p.e V g x ∧ (x : AE D) = p.ι (Matrix.GeneralLinearGroup.det gk : k) + (1 - p.e) := by
  intro D k _ _ _ _ p V Z _ _ F g gk hg
  have he : p.e * p.e = p.e := p.split.1
  refine ⟨GlobalTheory.SplitHecke.detU he V g, GlobalTheory.SplitHecke.isDetAt_detU he V g, ?_⟩
  have h0 : ((GlobalTheory.SplitHecke.detU he V g : (AE D)ˣ) : AE D) = p.e * (mt V g).det + (1 - p.e) :=
    GlobalTheory.SplitHecke.isDetAt_detU he V g
  rw [h0]
  congr 1
  have hc := GlobalTheory.LocMod.Witness.card_frame F
  let σ : Fin V.rank ≃ Z := (Fintype.equivFinOfCardEq hc.symm).symm
  let P : Matrix (Fin V.rank) (Fin V.rank) k := F.β.submatrix id σ
  let Q : Matrix (Fin V.rank) (Fin V.rank) k := F.γ.submatrix σ id
  let G : Matrix (Fin V.rank) (Fin V.rank) k := gk.val.submatrix σ σ
  have hPQ : P * Q = 1 := by
    simp only [P, Q]
    rw [Matrix.submatrix_mul_equiv, F.βγ, Matrix.submatrix_id_id]
  have hPGQ : P * G * Q = F.β * gk.val * F.γ := by
    simp only [P, Q, G]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hdet : p.π (mt V g).det = (Matrix.GeneralLinearGroup.det gk : k) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hg.2, ← hPGQ, Matrix.det_mul, Matrix.det_mul,
      mul_right_comm, ← Matrix.det_mul, hPQ, Matrix.det_one, one_mul, Matrix.det_submatrix_equiv_self,
      Matrix.GeneralLinearGroup.val_det_apply]
  rw [← hdet, p.ι_π]

theorem map_mt_inv_loc {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {V : HSp D} {Z : Type} [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z) (a : GA D V) (ak : GL Z k)
    (ha : (mt V a).map p.π = F.β * (ak : Matrix Z Z k) * F.γ) :
    (mt V a⁻¹).map p.π = F.β * ((ak⁻¹ : GL Z k) : Matrix Z Z k) * F.γ := by
  have h1 : (mt V a⁻¹).map p.π * (mt V a).map p.π = 1 := by
    rw [← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (F.β * (ak : Matrix Z Z k) * F.γ) * (F.β * ((ak⁻¹ : GL Z k) : Matrix Z Z k) * F.γ) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.γ F.β, F.γβ, Matrix.one_mul, ← Matrix.mul_assoc (ak : Matrix Z Z k), ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul, F.βγ]
  rw [ha] at h1
  calc (mt V a⁻¹).map p.π = (mt V a⁻¹).map p.π * ((F.β * (ak : Matrix Z Z k) * F.γ) *
        (F.β * ((ak⁻¹ : GL Z k) : Matrix Z Z k) * F.γ)) := by rw [h2, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem actO_up_of_map {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (a : GA D S) (A : Matrix Y' Y' k) (b : GA D T) (B : Matrix Y Y k)
    (hb : (mt T b).map p.π = FT.β * B * FT.γ) (ha : (mt S a⁻¹).map p.π = FS.β * A * FS.γ) (x : Matrix Y Y' k) :
    actO S T a b (p.up FS FT x) = p.up FS FT (B * x * A) := by
  have hh : IsHalf p.e (actO S T a b (p.up FS FT x)) :=
    GlobalTheory.SplitHecke.isHalf_actO a b (GlobalTheory.LocMod.Witness.up_half p FS FT x)
  rw [← GlobalTheory.LocMod.Witness.up_down p FS FT hh]
  congr 1
  have hx : (p.up FS FT x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = FT.β * x * FS.γ :=
    Matrix.ext fun _ _ => p.π_ι _
  unfold Place.down actO
  rw [Matrix.map_mul, Matrix.map_mul, hb, ha, hx]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc FT.γ, FT.γβ, Matrix.one_mul, ← Matrix.mul_assoc FT.γ, FT.γβ, Matrix.one_mul,
    ← Matrix.mul_assoc FS.γ, FS.γβ, Matrix.one_mul, Matrix.mul_one]

theorem actO_up_loc : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (a : GA D S) (ak : GL Y' k) (b : GA D T) (bk : GL Y k), p.IsLoc FS a ak → p.IsLoc FT b bk → ∀ x : Matrix Y Y' k, actO S T a b (p.up FS FT x) = p.up FS FT ((bk : Matrix Y Y k) * x * ((ak⁻¹ : GL Y' k) : Matrix Y' Y' k)) ∧ actO S T a⁻¹ b⁻¹ (p.up FS FT x) = p.up FS FT (((bk⁻¹ : GL Y k) : Matrix Y Y k) * x * (ak : Matrix Y' Y' k)) := by
  intro D k _ _ _ _ p S T Y Y' _ _ _ _ FS FT a ak b bk ha hb x
  refine ⟨actO_up_of_map p FS FT a _ b _ hb.2 (map_mt_inv_loc p FS a ak ha.2) x, ?_⟩
  refine actO_up_of_map p FS FT a⁻¹ _ b⁻¹ _ (map_mt_inv_loc p FT b bk hb.2) ?_ x
  rw [inv_inv]
  exact ha.2

open GlobalTheory.SplitScalar GlobalTheory.LocMod.Witness in
theorem vacuum_move : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (μS μT : kˣ →* ℂˣ), p.IsComp χS μS → p.IsComp χT μT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)), p.IsModel ψ FS FT Tm → ∀ (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), p.IsLoc FS g gk → p.IsLoc FT h hk → Enl gk hk → ∃ Φ₀ Φ₀' : SB (Matrix Y Y' k), Φ₀ ≠ 0 ∧ Φ₀'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ₀.1 ∧ ω (g, h) (Tm Φ₀) = Tm Φ₀' := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW μS μT hμS hμT Y Y' _ _ _ _ FS FT Tm hTm g gk h hk hg hh he
  classical
  obtain ⟨Λ, hdd, hd, hd', hup, hhalf, hchalf⟩ := GlobalTheory.T.localSelfDualLattice_split_place_decomposition D k p ψ hW.std S T Y Y' FS FT
  obtain ⟨R₀, hcard, hR₀, hR₀u⟩ := GlobalTheory.T.index_integralMatrices_in_substitution_image k Y Y' gk hk he
  have hact : ∀ x, actO S T g⁻¹ h⁻¹ (p.up FS FT x) =
      p.up FS FT (((hk⁻¹ : GL Y k) : Matrix Y Y k) * x * (gk : Matrix Y' Y' k)) :=
    fun x => (actO_up_loc D k p S T Y Y' FS FT g gk h hk hg hh x).2
  have up_sub : ∀ x y, p.up FS FT (x - y) = p.up FS FT x - p.up FS FT y := fun x y => map_sub (upH p FS FT) x y
  have up_inj : Function.Injective (p.up FS FT) := fun x y hxy => by
    rw [← down_up p FS FT x, hxy, down_up]
  obtain ⟨x, hx, hxv⟩ := exists_detAt_loc D k p S Y' FS g gk hg
  obtain ⟨y, hy, hyv⟩ := exists_detAt_loc D k p T Y FT h hk hh
  have hχx : ((μT (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) = χT x := hμT _ _ hxv
  have hχy : ((μS (Matrix.GeneralLinearGroup.det hk) : ℂˣ) : ℂ) = χS y := hμS _ _ hyv
  have hR : ∀ u ∈ R₀.image (p.up FS FT), actO S T g⁻¹ h⁻¹ u ∈ Λ ∧ IsHalf p.e u := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hu
    exact ⟨by rw [hact, hup]; exact hR₀ v hv, up_half p FS FT v⟩
  have hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ Λ → IsHalf p.e w → ∃! v, v ∈ R₀.image (p.up FS FT) ∧ w - v ∈ Λ := by
    intro w hw hwh
    obtain ⟨z, rfl⟩ : ∃ z, w = p.up FS FT z := ⟨_, (up_down p FS FT hwh).symm⟩
    rw [hact, hup] at hw
    obtain ⟨v, ⟨hv, hv2⟩, hvu⟩ := hR₀u z hw
    refine ⟨p.up FS FT v, ⟨Finset.mem_image_of_mem _ hv, by rw [← up_sub, hup]; exact hv2⟩, ?_⟩
    rintro u ⟨hu, hu2⟩
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.1 hu
    rw [← up_sub, hup] at hu2
    rw [hvu v' ⟨hv', hu2⟩]
  have hle : ∀ w ∈ Λ, IsHalf p.e w → actO S T g⁻¹ h⁻¹ w ∈ Λ := by
    intro w hw hwh
    obtain ⟨z, hz, rfl⟩ := hhalf w hw hwh
    rw [hact, hup]
    exact he z hz
  obtain ⟨r, hr, hom⟩ := GlobalTheory.SplitHecke.om_eq_smul_sum hW p.split hdd hd hd' hg.1 hh.1 hx hy hR hRu hle
  let ind : GL Y' k → GL Y k → Matrix Y Y' k → SB (Matrix Y Y' k) := fun a b v => ⟨_, indicator_mem_sb k Y Y' a b v⟩
  have ind_apply : ∀ a b v t, (ind a b v).1 t =
      if (∀ r q, ((b : Matrix Y Y k) * (t + v) * (a : Matrix Y' Y' k)) r q ∈ 𝒪[k]) then 1 else 0 := fun a b v t => by
    simp only [ind, Set.indicator_apply, Set.mem_setOf_eq]
  have hΦ₀ : ∀ t, (ind 1 1 0).1 t = if (∀ r q, t r q ∈ 𝒪[k]) then 1 else 0 := fun t => by
    rw [ind_apply]; simp
  have hΦv : ∀ v t, (ind 1 1 v).1 t = (ind 1 1 0).1 (t + v) := fun v t => by
    rw [ind_apply, ind_apply, add_zero]
  have hΦB : ∀ t, (ind gk hk⁻¹ 0).1 t = if (∀ r q, (((hk⁻¹ : GL Y k) : Matrix Y Y k) * t * (gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]) then 1 else 0 :=
    fun t => by rw [ind_apply]; simp
  have hsub : ∀ (a b : Matrix Y Y' k), (∀ r q, a r q ∈ 𝒪[k]) → (∀ r q, b r q ∈ 𝒪[k]) → ∀ r q, (a - b) r q ∈ 𝒪[k] :=
    fun a b ha hb r q => by rw [Matrix.sub_apply]; exact sub_mem (ha r q) (hb r q)
  have hf1 : ∀ u ∈ Λ, IsHalf p.e u → heisO ψ S T u (Tm (ind 1 1 0)) = Tm (ind 1 1 0) := by
    intro u hu huh
    obtain ⟨z, hz, rfl⟩ := hhalf u hu huh
    refine (hTm.trans z _ _ fun t => ?_).symm
    rw [hΦ₀, hΦ₀]
    refine if_congr ⟨fun h r q => ?_, fun h r q => ?_⟩ rfl rfl
    · rw [Matrix.add_apply]; exact add_mem (h r q) (hz r q)
    · have := hsub _ _ h hz r q
      rwa [add_sub_cancel_right] at this
  have hf2 : ∀ u ∈ Λ, IsHalf (cA D p.e) u → heisO ψ S T u (Tm (ind 1 1 0)) = Tm (ind 1 1 0) := by
    intro u hu huh
    refine (hTm.modul u huh _ _ fun t => ?_).symm
    by_cases ht : ∀ r q, t r q ∈ 𝒪[k]
    · rw [hchalf u hu huh t ht, one_mul]
    · rw [hΦ₀, if_neg ht, mul_zero]
  have key := hom _ (hTm.theta _) hf1 hf2
  have hsum : ∑ u ∈ R₀.image (p.up FS FT), heisO ψ S T u (Tm (ind 1 1 0)) = Tm (ind gk hk⁻¹ 0) := by
    rw [Finset.sum_image fun a _ b _ hab => up_inj hab]
    have e1 : ∀ v ∈ R₀, heisO ψ S T (p.up FS FT v) (Tm (ind 1 1 0)) = Tm (ind 1 1 v) :=
      fun v _ => (hTm.trans v _ _ fun t => hΦv v t).symm
    rw [Finset.sum_congr rfl e1, ← map_sum]
    congr 1
    refine Subtype.ext (funext fun t => ?_)
    rw [Submodule.coe_sum, Finset.sum_apply, hΦB]
    rw [Finset.sum_congr rfl fun v _ => by rw [hΦv, hΦ₀]]
    split_ifs with htB
    · have hnt : ∀ r q, (((hk⁻¹ : GL Y k) : Matrix Y Y k) * (-t) * (gk : Matrix Y' Y' k)) r q ∈ 𝒪[k] := fun r q => by
        rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]; exact neg_mem (htB r q)
      obtain ⟨v, ⟨hv, hv2⟩, hvu⟩ := hR₀u (-t) hnt
      have iff1 : ∀ v', (∀ r q, (-t - v') r q ∈ 𝒪[k]) ↔ (∀ r q, (t + v') r q ∈ 𝒪[k]) := fun v' => by
        refine forall_congr' fun r => forall_congr' fun q => ?_
        rw [show -t - v' = -(t + v') by abel, Matrix.neg_apply, neg_mem_iff]
      rw [Finset.sum_eq_single_of_mem v hv, if_pos ((iff1 v).1 hv2)]
      intro v' hv' hne
      rw [if_neg]
      intro h'
      exact hne (hvu v' ⟨hv', (iff1 v').2 h'⟩)
    · refine Finset.sum_eq_zero fun v hv => if_neg fun h' => htB fun r q => ?_
      have h2 := he _ h' r q
      have h3 := hsub _ _ (he _ h') (hR₀ v hv) r q
      rwa [← Matrix.sub_mul, ← Matrix.mul_sub, add_sub_cancel_right] at h3
  have hsf : ((splitFacO χS χT x y : Circle) : ℂ) =
      (((μT (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) : ℂ) * (μS (Matrix.GeneralLinearGroup.det hk) : ℂ) := by
    rw [splitFacO, Circle.coe_mul, Circle.coe_inv, ← hχx, ← hχy, Units.val_inv_eq_inv_val]
  have npos : ∀ z : kˣ, 0 < nabs k z := fun z => by
    have h1 : distribHaarChar k z * distribHaarChar k z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : distribHaarChar k z ≠ 0 := left_ne_zero_of_mul_eq_one h1
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 h2)
  refine ⟨ind 1 1 0, ((((μT (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) : ℂ) * (μS (Matrix.GeneralLinearGroup.det hk) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ ((Fintype.card Y : ℝ) / 2) : ℝ) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ (-(Fintype.card Y' : ℝ) / 2) : ℝ) : ℂ)) • ind gk hk⁻¹ 0,
    fun h0 => ?_, ?_, ?_⟩
  · have := congrArg (fun F : SB (Matrix Y Y' k) => F.1 0) h0
    simp only [hΦ₀] at this
    simp at this
  · funext t
    rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hΦB]
    unfold om
    rw [hΦ₀]
    split_ifs
    · simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    · simp
  · rw [key, hsum, map_smul]
    by_cases hf0 : Tm (ind 1 1 0) = 0
    · have hB : Tm (ind gk hk⁻¹ 0) = 0 := by
        rw [← hsum, hf0]
        exact Finset.sum_eq_zero fun u _ => funext fun w => by simp [heisO]
      rw [hB, smul_zero, smul_zero]
    · congr 1
      have hpair : ∀ u ∈ R₀.image (p.up FS FT), ∀ u' ∈ R₀.image (p.up FS FT), u ≠ u' → ∃ (l : WO S T) (ε : ℂ),
          ‖ε‖ = 1 ∧ heisO ψ S T l (Tm (ind 1 1 0)) = ε • Tm (ind 1 1 0) ∧ ψ (symplO S T (u - u') l) ≠ 1 := by
        intro u hu u' hu' hne
        have hn : u - u' ∉ Λ := fun hm => hne ((hRu u (hR u hu).1 (hR u hu).2).unique
          ⟨hu, by rw [sub_self]; exact zero_mem _⟩ ⟨hu', hm⟩)
        obtain ⟨l, hl, hlh, hlne⟩ := hd _ (isHalf_sub (hR u hu).2 (hR u' hu').2) hn
        exact ⟨l, 1, norm_one, by rw [hf2 l hl hlh, one_smul], psi_skew_ne hlne⟩
      have hr' := om_sum_scale_eq D ψ S T χS χT ω hW g h _ (hTm.theta _) hf0 _ (Circle.norm_coe _) r hr _ hpair key
      rw [Finset.card_image_of_injective _ up_inj, hcard] at hr'
      have hA := npos (Matrix.GeneralLinearGroup.det hk)
      have hB := npos (Matrix.GeneralLinearGroup.det gk)
      have hsq : (Real.sqrt (nabs k (Matrix.GeneralLinearGroup.det hk) ^ (Fintype.card Y' : ℝ) *
          nabs k (Matrix.GeneralLinearGroup.det gk) ^ (-(Fintype.card Y : ℝ))))⁻¹ =
          nabs k (Matrix.GeneralLinearGroup.det gk) ^ ((Fintype.card Y : ℝ) / 2) *
          nabs k (Matrix.GeneralLinearGroup.det hk) ^ (-(Fintype.card Y' : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, Real.mul_rpow (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _),
          ← Real.rpow_mul hA.le, ← Real.rpow_mul hB.le, mul_inv, ← Real.rpow_neg hA.le, ← Real.rpow_neg hB.le, mul_comm]
        congr 2 <;> ring
      rw [hr', hsq, hsf]
      push_cast
      ring

end GlobalTheory.LocOm

end
