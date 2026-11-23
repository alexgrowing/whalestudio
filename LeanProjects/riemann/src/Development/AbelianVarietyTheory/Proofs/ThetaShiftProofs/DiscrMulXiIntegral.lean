import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralDiscrMulOfTraceInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup

noncomputable section

namespace GlobalTheory.XiIntegral

section Tangent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.L2.Pj.QAt GlobalTheory.ArcQ
open scoped CategoryTheory.Obj

def origin (R : Type) [CommRing R] : Over.mk (𝟙 (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem gtTanR_iff (ν : GtPt D (epsR R)) : GtTanR ν ↔ origin R ≫ ν.b = 1 ∧
    ∀ χ y J, Good D.P.L y J → val (ν.s χ) (origin R).left y J = 1 := by
  constructor
  · rintro ⟨g₀, h₀, h⟩
    obtain ⟨h₁, h₂⟩ := (ConstLie.isZero_iff_zeroAlong (ρ := origin R) h).1 h₀
    refine ⟨h₁, fun χ y J hJ => ?_⟩
    have := h₂ χ _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · rintro ⟨h₁, h₂⟩
    obtain ⟨g₀, h⟩ := ConstLie.exists_isPullGt (origin R) ν
    obtain ⟨b, v⟩ := (TorusModel.isPull_iff _ _ _).1 h
    exact ⟨g₀, ⟨b.trans h₁, fun χ => corr_of_val D.P.isLB fun y J hJ =>
      (v χ y J hJ).trans ((h₂ χ y J hJ).trans (val_one _).symm)⟩, h⟩

theorem gtTanR_of_isZero {ν : GtPt D (epsR R)} (h : ν.IsZero) : GtTanR ν := by
  have hb : ν.b = 1 := h.1
  exact (gtTanR_iff ν).2 ⟨by rw [hb, MonObj.comp_one], fun χ y J hJ => (val_corr hJ (h.2 χ) _).trans (val_one _)⟩

theorem gtTanR_of_scale {a : R} {ν ν' : GtPt D (epsR R)} (h : GtPt.IsPull (spMap (epsScaleR a)) ν ν')
    (ht : GtTanR ν) : GtTanR ν' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  have s : (origin R).left ≫ spMap (epsScaleR a) = (origin R).left :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun x => by simp [epsScaleR]))
  refine (gtTanR_iff ν').2 ⟨Over.OverMorphism.ext ?_, fun χ y J hJ => ?_⟩
  · rw [← h₁, Over.comp_left, Over.comp_left, h.1, ← Category.assoc, s]
  · refine (val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_)
    rw [s]
    exact h₂ χ y J hJ

theorem gtTanR_of_isAdd {ν ν' ν'' : GtPt D (epsR R)} (h : ν.IsAdd ν' ν'') (ht : GtTanR ν) (ht' : GtTanR ν') :
    GtTanR ν'' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  obtain ⟨h₁', h₂'⟩ := (gtTanR_iff ν').1 ht'
  have hb : ν''.b = ν.b * ν'.b := h.1
  refine (gtTanR_iff ν'').2 ⟨by rw [hb, MonObj.comp_mul, h₁, h₁', _root_.mul_one], fun χ y J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) (origin R).left).trans (val_mul hJ _ _ _))
  have c := val_cub D.cub (origin R) hJ (DegPre.cT D (epsR R) χ) ν.b ν'.b
  rw [h₁', (isCub_cubV D.cub hJ).face₃] at c
  have e' := (congrArg₂ (· * ·) rfl c).symm.trans (e.trans (congrArg₂ (· * ·) (h₂ χ y J hJ) (h₂' χ y J hJ)))
  simpa using e'

theorem gtTanR_of_gtComb {m : ℕ} {cf : Fin m → R} {e : Fin m → GtPt D (epsR R)} {ν : GtPt D (epsR R)}
    (h : GtComb cf e ν) (he : ∀ i, GtTanR (e i)) : GtTanR ν := by
  obtain ⟨u, p, hu, h₀, ha, rfl⟩ := h
  have : ∀ i, GtTanR (p i) := fun i => Fin.induction (gtTanR_of_isZero h₀)
    (fun j ih => gtTanR_of_isAdd (ha j) ih (gtTanR_of_scale (hu j) (he j))) i
  exact this _

end

end Tangent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem exists_intHom {E : Type} [Field E] [NumberField E] [IsCMField E] {K₁ : Type} [Field K₁] [NumberField K₁]
    (τK : E →+* K₁) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X) :
    ∃ φ : X →+ 𝓞 K₁, ∀ x, (φ x : K₁) = ((NumberField.discr E : ℤ) : K₁) * τK (cc (pairE ξ x)) := by
  obtain ⟨-, hadd, -, hint, -⟩ := GlobalTheory.ArcQ.pairE_properties E X ξ
  have hi : ∀ x, IsIntegral ℤ (((NumberField.discr E : ℤ) : K₁) * τK (cc (pairE ξ x))) := fun x => by
    have h := (hint x).map (τK.comp (IsCMField.complexConj E).toRingEquiv.toRingHom).toIntAlgHom
    simpa [cc] using h
  refine ⟨AddMonoidHom.mk' (fun x => ⟨_, hi x⟩) fun x y => ?_, fun x => rfl⟩
  apply RingOfIntegers.ext
  show _ * τK (cc (pairE ξ (x + y))) = _ * τK (cc (pairE ξ x)) + _ * τK (cc (pairE ξ y))
  rw [hadd]
  simp [cc, mul_add]

theorem discr_mul_xi_integral : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (ρ : 𝓞 K₁ →+* Tv.V) (ψ : M.aw.D₀.P.A.left ⟶ s.B.A.left), OverLa w Tv.V io 1 → (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → IsPolFibre ρ s.B M.aw.D₀.P ψ → prj M.pw ≫ ψ = prj M.pK ≫ s.φB → TauCan M.aw.D₀ n' → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)), s.kind τ k = none → ∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![((NumberField.discr E : ℤ) : Tv.Fr)] ![e₂] ν₁ := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s w Tv io Wl M ρ ψ _ hρ _ _ _ τ k hk
  have hG : Out.GlobalFnsSt := hK.laws.globalFns
  obtain ⟨φ, hφ⟩ := exists_intHom (labK c K₁ τ) s.ξ
  obtain ⟨hb, hd⟩ := s.xi τ k hk
  obtain ⟨hw1, -, hw3⟩ := GlobalTheory.TorusTangent.main hG Tv.V M.aw.D₀
  obtain ⟨-, -, hK3⟩ := GlobalTheory.TorusTangent.main hG K₁ d.a.D₀
  obtain ⟨hF1, hF2, -⟩ := GlobalTheory.TorusTangent.main hG Tv.Fr M.aK.D₀
  obtain ⟨-, hadd, -⟩ := GlobalTheory.ArcQ.pairE_properties E d.a.D₀.X s.ξ
  let φw : M.aw.D₀.X →+ Tv.V :=
    ρ.toAddMonoidHom.comp (φ.comp (M.pK.xe.toAddMonoidHom.comp M.pw.xe.symm.toAddMonoidHom))
  let φ₀ : d.a.D₀.X →+ K₁ := AddMonoidHom.mk' (fun x => labK c K₁ τ (cc (pairE s.ξ x))) fun x y => by
    rw [hadd]; simp [cc]
  let φ₂ : M.aK.D₀.X →+ Tv.Fr := io.toAddMonoidHom.comp (φ₀.comp M.pK.xe.toAddMonoidHom)
  obtain ⟨ν, ⟨hν, hνb, hνd⟩, -⟩ := hw1 φw
  obtain ⟨ν₁, h₁, -⟩ := GlobalTheory.ArcQBC.existsUnique_letBC M.pw hG ν
  obtain ⟨e₂, h₂, -⟩ := GlobalTheory.ArcQBC.existsUnique_letBC M.pK hG (d.e τ k)
  have t₁ := GlobalTheory.ArcQBC.gtTanR_of_letBC M.pw hG h₁ hν
  have t₂ := GlobalTheory.ArcQBC.gtTanR_of_letBC M.pK hG h₂ (s.tan τ k)
  obtain ⟨b₁, d₁⟩ := hw3 Tv.Fr M.aK.D₀ _ M.pw φw ν ν₁ hνb hνd h₁
  obtain ⟨b₂, d₂⟩ := hK3 Tv.Fr M.aK.D₀ _ M.pK φ₀ (d.e τ k) e₂ hb hd h₂
  obtain ⟨ν', hν'⟩ := GlobalTheory.ConstLie.exists_gtComb ![((NumberField.discr E : ℤ) : Tv.Fr)] ![e₂]
  have t₃ : GtTanR ν' := gtTanR_of_gtComb hν' fun i => by fin_cases i; exact t₂
  obtain ⟨b₃, d₃⟩ := hF2 φ₂ _ e₂ ν' t₂ b₂ d₂ hν'
  have key : ∀ x, algebraMap Tv.V Tv.Fr (φw (M.pw.xe x)) = (((NumberField.discr E : ℤ) : Tv.Fr) • φ₂) x := fun x => by
    show algebraMap Tv.V Tv.Fr (ρ (φ (M.pK.xe (M.pw.xe.symm (M.pw.xe x))))) =
      ((NumberField.discr E : ℤ) : Tv.Fr) * io (labK c K₁ τ (cc (pairE s.ξ (M.pK.xe x))))
    rw [AddEquiv.symm_apply_apply, hρ, hφ, map_mul, map_intCast]
  have e : ν₁ = ν' := (hF1 (((NumberField.discr E : ℤ) : Tv.Fr) • φ₂)).unique
    ⟨t₁, b₁, fun x j hj => (d₁ x j hj).trans (congrArg _ (key x))⟩ ⟨t₃, b₃, d₃⟩
  exact ⟨ν, ν₁, e₂, hν, h₁, h₂, e ▸ hν'⟩

end GlobalTheory.XiIntegral
