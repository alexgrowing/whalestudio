import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SourceLiftAtGluedPlaceProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearEquivariantOrthogonalSummandLift
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcExact

section Det

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n' : Type} [Fintype n'] [DecidableEq n']

theorem length_residue : Module.length 𝒪[k] 𝓀[k] = 1 := by
  rw [Module.length_eq_one_iff]
  exact isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 (maximalIdeal.isMaximal _))

theorem fn_surjective (P : Pair k n') : Function.Surjective P.fn := by
  intro a
  obtain ⟨x, hx⟩ : ∃ x, P.fn x ≠ 0 := by
    by_contra h
    push_neg at h
    exact P.fn_ne (LinearMap.ext h)
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (a * (P.fn x)⁻¹)
  refine ⟨s • x, ?_⟩
  rw [map_smul, Algebra.smul_def, ResidueField.algebraMap_eq, hs, mul_assoc, inv_mul_cancel₀ hx, mul_one]

set_option synthInstance.maxHeartbeats 200000 in

theorem valuation_det_mul_unif (q : Unif k) (P : Pair k n') (g : GL n' k) (hg : g • P.ker = P.lat) :
    valuation k (((Matrix.GeneralLinearGroup.det g : kˣ) : k) * (q.unit : k)) = 1 := by
  classical
  have hmem : ∀ x ∈ P.lat, g⁻¹ • x ∈ P.ker := fun x hx => mem_smul_iff.1 (hg ▸ hx)
  let F : (n' → k) →ₗ[𝒪[k]] (n' → k) := (Matrix.toLin' (g⁻¹ : GL n' k).val).restrictScalars 𝒪[k]
  have hF : ∀ x, F x = g⁻¹ • x := fun x => rfl
  have hFm : ∀ x ∈ P.lat, F x ∈ P.lat := fun x hx => P.ker_le (by rw [hF]; exact hmem x hx)
  let f : P.lat →ₗ[𝒪[k]] P.lat := F.restrict hFm
  have hr : LinearMap.range f = LinearMap.ker P.fn := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (Pair.mem_ker.1 (hmem y y.2)).2
    · intro hx
      have h1 : (x : n' → k) ∈ P.ker := Pair.mem_ker.2 ⟨x.2, hx⟩
      have h2 : g • (x : n' → k) ∈ g • P.ker := mem_smul_iff.2 (by rwa [inv_smul_smul])
      rw [hg] at h2
      refine ⟨⟨_, h2⟩, Subtype.ext ?_⟩
      change F (g • (x : n' → k)) = x
      rw [hF, inv_smul_smul]
  have hlen : IsDiscreteValuationRing.addVal 𝒪[k] (LinearMap.det f) = 1 := by
    rw [← GlobalTheory.length_quotient_range_eq_addVal_det, hr, (P.fn.quotKerEquivOfSurjective (fn_surjective P)).length_eq,
      length_residue]
  have hdetmap : algebraMap 𝒪[k] k (LinearMap.det f) = ((g⁻¹ : GL n' k) : Matrix n' n' k).det := by
    let b := Module.finBasis 𝒪[k] P.lat
    let bK := b.extendOfIsLattice k
    have hbK : ∀ i, bK i = (b i : n' → k) := Module.Basis.extendOfIsLattice_apply k b
    rw [← LinearMap.det_toMatrix b f, RingHom.map_det,
      ← LinearMap.det_toLin' ((g⁻¹ : GL n' k) : Matrix n' n' k), ← LinearMap.det_toMatrix bK]
    refine congrArg Matrix.det ?_
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have e1 : Matrix.toLin' (g⁻¹ : GL n' k).val (bK j) = ((f (b j) : P.lat) : n' → k) := by rw [hbK]; rfl
    have e2 : ((f (b j) : P.lat) : n' → k) = ∑ l, algebraMap 𝒪[k] k (b.repr (f (b j)) l) • bK l := by
      have h := congrArg Subtype.val (b.sum_repr (f (b j)))
      rw [← h, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Submodule.coe_smul, hbK, algebraMap_smul]
    rw [e1, e2, bK.repr_sum_self]
  obtain ⟨u, hu⟩ := (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).1
    (hlen.trans (IsDiscreteValuationRing.addVal_uniformizer q.2).symm)
  have hdg : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) * (q.unit : k) = ((u : 𝒪[k]) : k) := by
    have h1 := congrArg (algebraMap 𝒪[k] k) hu
    rw [map_mul, hdetmap] at h1
    have h2 : ((g⁻¹ : GL n' k) : Matrix n' n' k).det = ((Matrix.GeneralLinearGroup.det g : kˣ) : k)⁻¹ := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val]
    rw [h2] at h1
    have h3 : (q.unit : k) = algebraMap 𝒪[k] k q.1 := rfl
    rw [h3, ← h1, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
    rfl
  rw [hdg]
  have h1 : valuation k ((u : 𝒪[k]) : k) ≤ 1 := (u : 𝒪[k]).2
  have h2 : valuation k (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) ≤ 1 := ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]).2
  have h3 : valuation k ((u : 𝒪[k]) : k) * valuation k (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) = 1 := by
    rw [← map_mul]
    have : ((u : 𝒪[k]) : k) * (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]
      rfl
    rw [this, map_one]
  refine le_antisymm h1 ?_
  calc (1 : ValueGroupWithZero k) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

end Det

end GlobalTheory.FinPl.SrcExact

namespace GlobalTheory.FinPl.SrcExact

open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl GlobalTheory.FinPl.SrcTheta

variable {D : D7}

theorem Frame.rank_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) :
    S.rank = Fintype.card n := by
  let e : (n → k) ≃ₗ[k] (Fin S.rank → k) := LinearEquiv.ofLinear (Matrix.toLin' β.b) (Matrix.toLin' β.b')
    (by rw [← Matrix.toLin'_mul, β.bb', Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, β.b'b, Matrix.toLin'_one])
  have := e.finrank_eq
  rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at this
  exact this.symm

theorem chrPow_neg_one_mul (χ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) : chrPow χ a (-1) * chrPow χ a 1 = 1 := by
  simp only [chrPow, ← Circle.coe_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Circle.coe_one]

end GlobalTheory.FinPl.SrcExact

namespace GlobalTheory.FinPl.SrcExact

open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl GlobalTheory.FinPl.SrcTheta

theorem exists_theta_exact {D : D7} (hLin : LinExact D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L)
    (hA : CoCpt A) (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (hW : IsWeilDatumO ψ S T χS χT om)
    (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) {ζ : Fin L.rank → D.host.E}
    (hsum : IsSumFrame o ζ α α₀) :
    ∃ lS : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧
      (lS q.unit : ℂ) = (((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2) : ℝ) : ℂ) * chrPow χT (p.idele q.unit) (-1) ∧
      ∀ (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → Vac ψ S T LS LT (· = p.v) f₀ →
        ∃ θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ),
          (∀ (v : CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ) (f : WO S T → ℂ), Over ψ α₀ β LS LT f₀ Φ f →
            θ v Φ = liftA o om vA v f) ∧
          ∀ (g : GL n' k) (v : CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) →
            θ (caRep α g v) (fun x => Φ (x * (blk g).val)) =
              ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ := by
  obtain ⟨lS, lT, hlS, -, hq, -, hEq⟩ := hLin k p q ψ S T χS χT om hW
  obtain ⟨_, _, -, -, hlin⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW
  refine ⟨lS, hlS, hq, fun LS LT f₀ hLS hLT hvac => ?_⟩
  obtain ⟨hex, hth, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hW.std S T α₀ β LS LT hLS hLT f₀ hvac
  obtain ⟨G, hG, hGP⟩ := exists_linear_of_rel (SB (Matrix n (n' ⊕ Fin 1) k)) (Over ψ α₀ β LS LT f₀) hex
    (fun c x y x' y' h h' => (hlin n _ α₀ β LS LT f₀ x y h).2.2 c x' y' h')
  have hGt : ∀ Φ, IsThetaFunO ψ S T (G Φ) := fun Φ => (hG Φ).elim fun x hx => (hth _ _ hx).1
  have hGf : ∀ Φ f, Over ψ α₀ β LS LT f₀ Φ f → G Φ = f := fun Φ f h =>
    (hex Φ h.2.2.2.1).unique (hGP Φ h.2.2.2.1) h
  let θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Φ => liftA o om vA v (G Φ))
      (fun v v' Φ => liftA_add_left o hA vA hW v.2 v'.2 (hGt Φ))
      (fun c v Φ => liftA_smul_left o vA c v (G Φ))
      (fun v Φ Φ' => by rw [map_add]; exact liftA_add_right o hA vA hW v.2 (hGt Φ) (hGt Φ'))
      (fun c v Φ => by rw [map_smul]; exact liftA_smul_right o vA c v (G Φ))
  have hθ : ∀ (v : CA A) Φ, θ v Φ = liftA o om vA v (G Φ) := fun _ _ => rfl
  refine ⟨θ, fun v Φ f h => by rw [hθ, hGf Φ f h], fun g v Φ hΦ => ?_⟩
  have h1 := hEq n _ α₀ β LS LT f₀ Φ _ (hGP Φ hΦ) (blk g) 1
  have hdet : Matrix.GeneralLinearGroup.det (blk g) = Matrix.GeneralLinearGroup.det g := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have hemb : α₀.gl (blk g) = o.emb (α.gl g, 1) := by
    rw [Comm.emb_gl hsum]
    congr 1
  have hfun : (fun x : Matrix n (n' ⊕ Fin 1) k => (lS (Matrix.GeneralLinearGroup.det (blk g)) : ℂ) *
      (lT (Matrix.GeneralLinearGroup.det (1 : GL n k)) : ℂ) * Φ (((1 : GL n k)⁻¹ : GL n k).val * x * (blk g).val)) =
      (lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val) := by
    funext x
    simp only [hdet, map_one, Units.val_one, mul_one, inv_one, Matrix.one_mul, Pi.smul_apply, smul_eq_mul]
  rw [hfun, hemb, map_one] at h1
  have h2 : θ (caRep α g v) ((lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val)) = θ v Φ := by
    rw [hθ, hθ, hGf _ _ h1]
    exact liftA_equiv o vA hW v.2 (hGt Φ) (α.gl g)
  rw [← h2, map_smul, inv_smul_smul₀ (Units.ne_zero _)]

end GlobalTheory.FinPl.SrcExact

open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl GlobalTheory.FinPl.SrcExact in

theorem GlobalTheory.FinPl.sourceExact : ∀ D : D7, GlobalTheory.FinPl.SourceExact D := by
  intro D k _ _ _ _ p n n' _ _ _ _ q χ₀ hχ
  have hQ : (0 : ℝ) < resCard k := by
    have : 0 < resCard k := Nat.card_pos
    exact_mod_cast this
  refine ⟨((resCard k : ℝ) ^ Fintype.card n)⁻¹ * (resCard k : ℝ) ^ ((Fintype.card n : ℝ) / 2), 1,
    mul_pos (inv_pos.2 (pow_pos hQ _)) (Real.rpow_pos_of_pos hQ _), ?_⟩
  intro ψ S A L T o ζ hL hA vA χS χT om hW _ hT α α₀ β hsum P Λ _ LS LT f₀ Ξ Ξ' hΞ hΞ' φ hφ
  set χ := resChar χ₀ hχ q with hχχ
  obtain ⟨lS, hlS, hq, hθ⟩ :=
    exists_theta_exact (GlobalTheory.T.linearModel_splitPlace_characterEquivariance D) k p n n' q ψ S A L T o hA vA χS χT om hW α α₀ β hsum
  have hdet : ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsLattice k → ∀ g ∈ latStab L',
      ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 1 := fun L' hL' g hg => by
    rw [GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n' L' hL' g hg lS (hlS hT), Units.val_one]
  have hsb := GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts k n n'

  have hinv : ∀ (θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ)),
      (∀ (g : GL n' k) (v : CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) →
        θ (caRep α g v) (fun x => Φ (x * (blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ) →
      ∀ a ∈ SB (n → k), ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsLattice k →
        GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.IsLiftInv (caRep α) (θ.compl₂ (tensL a)) L' := by
    intro θ hθe a ha L' hL' g hg v Ψ hΨ
    simp only [LinearMap.compl₂_apply, tensL_apply]
    have := hθe g v _ (hsb.1 Ψ a hΨ ha)
    rw [hdet L' hL' g hg, inv_one, one_smul] at this
    refine Eq.trans (congrArg _ ?_) this
    funext x
    exact (tensCol_mul_blk Ψ a g x).symm
  obtain ⟨P', hP'⟩ := exists_lat_eq P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n' k) P' P

  have hc : ((resCard k : ℂ) ^ Fintype.card n)⁻¹ * ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) =
      ((((resCard k : ℝ) ^ Fintype.card n)⁻¹ * (resCard k : ℝ) ^ ((Fintype.card n : ℝ) / 2) : ℝ) : ℂ) *
        chrPow χT (p.idele q.unit) 1 := by
    have hv := valuation_det_mul_unif q P g (by rw [← hP', ← Pair.smul_lat, hg])
    have h1 : lS (Matrix.GeneralLinearGroup.det g * q.unit) = 1 := hlS hT _ (by rw [Units.val_mul]; exact hv)
    rw [map_mul] at h1
    have h2 : ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * (lS q.unit : ℂ) = 1 := by
      rw [← Units.val_mul, h1, Units.val_one]
    rw [hq, Frame.rank_eq β] at h2
    have h3 : (resCard k : ℝ) ^ (-(Fintype.card n : ℝ) / 2) * (resCard k : ℝ) ^ ((Fintype.card n : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hQ, neg_div, neg_add_cancel, Real.rpow_zero]
    have h4 := chrPow_neg_one_mul χT (p.idele q.unit)
    have hyz : ((((resCard k : ℝ) ^ (-(Fintype.card n : ℝ) / 2) : ℝ) : ℂ) * chrPow χT (p.idele q.unit) (-1)) *
        ((((resCard k : ℝ) ^ ((Fintype.card n : ℝ) / 2) : ℝ) : ℂ) * chrPow χT (p.idele q.unit) 1) = 1 := by
      rw [mul_mul_mul_comm, ← Complex.ofReal_mul, h3, Complex.ofReal_one, one_mul, h4]
    have h5 : ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) =
        (((resCard k : ℝ) ^ ((Fintype.card n : ℝ) / 2) : ℝ) : ℂ) * chrPow χT (p.idele q.unit) 1 := by
      calc _ = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            (((((resCard k : ℝ) ^ (-(Fintype.card n : ℝ) / 2) : ℝ) : ℂ) * chrPow χT (p.idele q.unit) (-1)) *
              ((((resCard k : ℝ) ^ ((Fintype.card n : ℝ) / 2) : ℝ) : ℂ) * chrPow χT (p.idele q.unit) 1)) := by
            rw [hyz, mul_one]
        _ = _ := by rw [← mul_assoc, h2, one_mul]
    rw [h5, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast]
    ring
  rw [← hc]
  obtain ⟨θ, hθv, hθe⟩ := hθ LS LT f₀ hΞ.1 hΞ.2.1 hΞ.2.2.1
  obtain ⟨hram, heq⟩ := toCA_ram hφ
  set φc := toCA φ hφ.2.2 with hφc
  have hχ1 : χ ≠ 1 := hχχ ▸ resChar_ne_one hχ q
  rw [show liftA o om vA (φ P) Ξ = θ (φc P) _ from (hθv (φc P) _ _ hΞ).symm,
    ((GlobalTheory.T.gluedLattice_finite_expansions_localField k n n' q χ hχ1 Λ).1 P).1]
  have e0 : θ (φc P) (tensCol (latInd P.ker Λ) (vecInd Λ)) = 0 :=
    GlobalTheory.LastSteps.lift_latInd P hram heq (hinv θ hθe _ (hsb.2.1 Λ inferInstance) P.ker inferInstance) Λ
  have e1 : ∀ Q ∈ withLat Λ, θ (φc P) (tensCol (latInd P.ker Q.ker + GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mainDatum q χ 1 P Q)
      (charInd χ Q)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • liftA o om vA (FFStar q χ φ P) (Ξ' Q) := by
    intro Q hQ
    have hI := hinv θ hθe _ (hsb.2.2 χ Q) P.ker inferInstance
    have a0 : θ (φc P) (tensCol (latInd P.ker Q.ker) (charInd χ Q)) = 0 :=
      GlobalTheory.LastSteps.lift_latInd P hram heq hI Q.ker
    have a1 := GlobalTheory.LastSteps.lift_mainDatum q χ 1 heq hI Q rfl hP'
    simp only [LinearMap.compl₂_apply, tensL_apply, map_one, Module.End.one_apply] at a1
    have a2 := hθe g⁻¹ (FFStar q χ φc P) _ (hΞ' Q hQ).2.2.2.1
    have b1 : caRep α g⁻¹ (FFStar q χ φc P) = FFStar q χ φc P' := by
      rw [← hg, FFStar_mem_EqForm q χ heq g P', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have b2 : (fun x => tensCol (phiOne P Q) (charInd χ Q) (x * (blk g⁻¹).val)) = tensCol (phiOne P' Q) (charInd χ Q) := by
      funext x
      rw [tensCol_mul_blk]
      congr 1
      funext x₀
      rw [← hg, phiOne_smul_left, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [b1, b2, hθv _ _ _ (hΞ' Q hQ), coe_FFStar] at a2
    rw [tensCol_add, map_add, a0, zero_add, a1, a2, map_inv, map_inv, Units.val_inv_eq_inv_val, inv_inv]
    rfl
  rw [map_smul, map_add, map_sum, e0, zero_add, Finset.sum_congr rfl e1, ← Finset.smul_sum, smul_smul]
