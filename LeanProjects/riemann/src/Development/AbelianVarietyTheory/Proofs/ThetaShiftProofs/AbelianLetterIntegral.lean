import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsSplit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SplitBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralOfLocalGenerator
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcPointTangentPart
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.EquivIffOfIsEmpty

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.EtaInt

open GlobalTheory.CM.IntCoord (sc)

theorem sc_mul {S : Type} [CommRing S] (s t : S) : sc s ≫ sc t = sc (s * t) := by
  refine Over.OverMorphism.ext ((spMap_comp_spMap _ _).trans ?_)
  show spMap _ = spMap _
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR, _root_.mul_assoc]

theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  refine (spMap_comp_spMap _ _).trans ?_
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem sc_over {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} {G : Over (Sp A)} {G' : Over (Sp B)}
    {φ : G'.left ⟶ G.left} {v : epsR A ⟶ G} {v' : epsR B ⟶ G'} (h : v'.left ≫ φ = spMap (dualMap f) ≫ v.left) (a : A) :
    (sc (f a) ≫ v').left ≫ φ = spMap (dualMap f) ≫ (sc a ≫ v).left := by
  show (spMap (epsScaleR (f a)) ≫ v'.left) ≫ φ = spMap (dualMap f) ≫ spMap (epsScaleR a) ≫ v.left
  rw [Category.assoc, h, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ v.left) (LieCombBaseChange.dualMap_epsScale f a).symm

theorem eq_sc_of_isLieComb {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G] {n : ℕ} {v : Fin n → (epsR S ⟶ G)}
    {c : Fin n → S} {a : S} {u w : epsR S ⟶ G} (hu : IsLieComb c v u) (hw : IsLieComb (a • c) v w) : w = sc a ≫ u := by
  rw [CM.IntCoord.isLieComb_iff] at hu hw
  have e := map_list_prod (preHom (G := G) (sc a)) (List.ofFn fun i => sc (c i) ≫ v i)
  rw [List.map_ofFn, ← hu] at e
  refine hw.trans (Eq.trans ?_ e.symm)
  congr 2
  funext i
  show sc (a * c i) ≫ v i = sc a ≫ sc (c i) ≫ v i
  rw [← Category.assoc, sc_mul]

theorem isTangent_sc {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G] {v : epsR S ⟶ G} (h : IsTangent v) (a : S) :
    IsTangent (sc a ≫ v) := by
  show _ ≫ spMap (epsScaleR a) ≫ v.left = _
  rw [← Category.assoc, spMap_comp_spMap]
  refine Eq.trans (congrArg (fun q => spMap q ≫ v.left) (RingHom.ext fun x => ?_)) h
  simp [epsScaleR]

theorem c_pow_of_pull {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] {f : A →+* B}
    {D : Out.DegPre A} {D' : Out.DegPre B} (p : Out.IsPullDeg f D D') {n : ℕ} (h : ∀ y, D.c y ^ n = 1) (y : D'.X) :
    D'.c y ^ n = 1 := by
  have gp := pull_grp p
  let U : Over.mk ((𝟙_ (Over (Sp B))).hom ≫ spMap f) ⟶ 𝟙_ (Over (Sp A)) := toUnit _
  have hU : U.left = spMap f := ((Category.comp_id _).symm.trans (Over.w U)).trans (Category.id_comp _)
  have e : pushHom gp _ (D'.c y) = preHom U (D.c (p.xe y)) :=
    Over.OverMorphism.ext ((p.c_pr y).trans (congrArg (· ≫ (D.c (p.xe y)).left) hU.symm))
  have e' : pushHom gp _ (D'.c y ^ n) = pushHom gp _ 1 := by
    rw [map_pow, e, ← map_pow, h, map_one, map_one]
  exact Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) e') ((Over.w _).trans (Over.w _).symm))

theorem lift_through_split (hK : Known) {K V F : Type} [CommRing K] [IsDomain K] [IsNoetherianRing K] [CommRing V]
    [IsDomain V] [IsNoetherianRing V] [CommRing F] [IsDomain F] [IsNoetherianRing F] {io : K →+* F} {j : V →+* F}
    (hio : Function.Injective io) (hj : Function.Injective j) {DK : Out.DegPre K} {DV : Out.DegPre V} {DF : Out.DegPre F}
    (pK : Out.IsPullDeg io DK DF) (pw : Out.IsPullDeg j DV DF) {n : ℕ} (hn : 0 < n) (hc : ∀ y, DV.c y ^ n = 1)
    {sB : ∀ T : Over (Sp K), (T ⟶ DK.P.A) → Out.GtPt DK T} (hs : IsSplit DK n sB) {u : epsR K ⟶ DK.P.A} {a : K}
    {e : Out.GtPt DK (epsR K)} (he : Out.GtPt.IsPull (spMap (epsScaleR a)) (sB _ u) e) {v : epsR V ⟶ DV.P.A}
    (hv : IsTangent v) {u₁ : epsR F ⟶ DF.P.A} (hu₁ : u₁.left ≫ prj pK = spMap (dualMap io) ≫ u.left) (x : F)
    (h : (sc (x * io a) ≫ u₁).left ≫ prj pw = spMap (dualMap j) ≫ v.left) :
    ∃ (ν : Out.GtPt DV (epsR V)) (ν₁ e₂ : Out.GtPt DF (epsR F)),
      GtTanR ν ∧ LetBC pw ν ν₁ ∧ LetBC pK e e₂ ∧ GtComb ![x] ![e₂] ν₁ := by
  obtain ⟨sV, hV⟩ := GlobalTheory.ArcCM.exists_isSplit hK V DV n hn hc
  obtain ⟨sF, hF⟩ := GlobalTheory.ArcCM.exists_isSplit hK F DF n hn (c_pow_of_pull pw hc)
  obtain rfl : e = sB _ (sc a ≫ u) := TorsionPairTest.isPull_unique he (hs.2.2 _ _ (sc a) u)
  obtain ⟨h₁, h₂⟩ := GlobalTheory.SplitBC.split_baseChange hK V F j DV DF pw n sV sF hj hV hF v _ h
  refine ⟨_, _, _, h₁ hv, h₂, (GlobalTheory.SplitBC.split_baseChange hK K F io DK DF pK n sB sF hio hs hF _ _ (sc_over hu₁ a)).2,
    ![sF _ (sc (x * io a) ≫ u₁)], ![sF _ 1, sF _ (sc (x * io a) ≫ u₁)], fun i => ?_, ?_, fun i => ?_, rfl⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hF.2.2 _ _ (sc x) (sc (io a) ≫ u₁)
    rw [← Category.assoc, sc_mul] at this
    exact this
  · have := hF.2.1 (epsR F) 1 1
    rw [_root_.mul_one] at this
    exact TanPart.isZero_of_isAdd this
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hF.2.1 (epsR F) 1 (sc (x * io a) ≫ u₁)
    rw [_root_.one_mul] at this
    exact this

theorem isUnit_of_notMem {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {Tv : CDVR}
    {io : K →+* Tv.Fr} {ρ : 𝓞 K →+* Tv.V} (ho : OverLa w Tv.V io 1)
    (hρ : ∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) : IsUnit (ρ s) := by
  have h1 : w.valuation K (s : K) = 1 := (w.valuation_eq_one_iff_notMem (K := K)).2 hs
  have h0 : (s : K) ≠ 0 := fun e => by rw [e, map_zero] at h1; exact zero_ne_one h1
  have h2 := ho.2 (s : K)
  rw [vLa, h1, vV] at h2
  have h3 : valV Tv.V (io (s : K)) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 h0)
  have h4 : valV Tv.V (io (s : K)) = 1 := by
    rw [← WithZero.exp_log h3]
    simp only [WithZero.log_one, neg_zero, mul_zero, neg_eq_zero] at h2
    rw [h2, WithZero.exp_zero]
  rw [← hρ] at h4
  have h5 := ((IsDiscreteValuationRing.maximalIdeal Tv.V).valuation_eq_one_iff_notMem (K := Tv.Fr)).1 h4
  by_contra hu
  exact h5 hu

theorem letter_unique {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c : Coeff l} {nΨ n' : ℕ} {o : LamObj c nΨ n'} (L : LamLetters o)
    (hB : IsFibreOf o.B o.xB (gmap o.K₁) o.φB) {k : Fin o.xB.P.g} {u u' : epsR o.K₁ ⟶ o.xB.P.A} (h : L.IsLetter k u)
    (h' : L.IsLetter k u') : u = u' := by
  refine Over.OverMorphism.ext (hB.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  unfold LamLetters.IsLetter at h h'
  rcases hs : L.src k with q | q <;> rw [hs] at h h' <;> exact h.trans h'.symm

theorem letter_integral {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c : Coeff l} {nΨ n' f : ℕ} {o : LamObj c nΨ n'} {La : ℝ}
    (ho : LamObjGood o f La) {L : LamLetters o} (hL : L.IsGood) (p : HeightOneSpectrum (𝓞 o.K₁)) {k : Fin o.xB.P.g}
    {cl : o.K₁} (hcl : IsLocGen p cl (L.ℓ k).I) {u : epsR o.K₁ ⟶ o.xB.P.A} (hu : L.IsLetter k u) :
    ∃ (s : 𝓞 o.K₁) (t : epsR (𝓞 o.K₁) ⟶ o.B.A), s ∉ p.asIdeal ∧ IsTangent t ∧
      (sc ((s : o.K₁) * cl) ≫ u).left ≫ o.φB = spMap (dualMap (algebraMap (𝓞 o.K₁) o.K₁)) ≫ t.left := by
  have hB := ho.2.2.2.1
  obtain ⟨M, hM, -⟩ := ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p
  have hf := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB o.φB).1 hB
  obtain ⟨s, hs, hm⟩ := (isModelAt_integral_iff_mem_lieLat _ o.B o.xB o.φB hf p M hM _).1
    (letter_integral_of_isLocGen E H l c nΨ n' f o La ho L hL p M hM k cl hcl)
  obtain ⟨t, ht, w, hw, hc⟩ := ((CM.integral_tangent_coordinates _ o.B _).2.2.2.2.1 _).1 hm
  obtain ⟨u', hu', hU⟩ := hL.2.2.1 k
  obtain rfl := letter_unique L hB hu hu'
  have e : s • cl • L.U k = ((s : o.K₁) * cl) • L.U k := by
    rw [mul_smul]; exact (algebraMap_smul o.K₁ s _).symm
  have hc' : IsLieComb (((s : o.K₁) * cl) • L.U k) o.xB.v w := e ▸ hc
  exact ⟨s, t, hs, ht, eq_sc_of_isLieComb hU hc' ▸ hw⟩

end GlobalTheory.ArcCM.EtaInt

namespace GlobalTheory.ArcCM

open EtaInt
open GlobalTheory.CM.IntCoord (sc)

theorem abelian_letter_integral : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (ρ : 𝓞 K₁ →+* Tv.V) (ψ : M.aw.D₀.P.A.left ⟶ s.B.A.left), OverLa w Tv.V io 1 → (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → IsPolFibre ρ s.B M.aw.D₀.P ψ → prj M.pw ≫ ψ = prj M.pK ≫ s.φB → TauCan M.aw.D₀ n' → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) (m : Fin d.a.D₀.P.g) (cl : K₁), s.kind τ k = some m → IsLocGen w cl (s.line τ k).I → ∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![io ((n' : K₁) * cl)] ![e₂] ν₁ := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s w Tv io Wl M ρ ψ ho hρ hψ hsq hτ τ k m cl hk hcl
  letI := H.starRing
  obtain ⟨u, hu, he⟩ := s.eta τ k m hk
  have hcl' : IsLocGen w cl (s.L.ℓ m).I := by
    have : s.line τ k = s.L.ℓ m := by unfold CMIn.line; rw [hk]; rfl
    exact this ▸ hcl
  obtain ⟨r, t, hr, ht, hrt⟩ := letter_integral s.good s.L_good w hcl' hu
  obtain ⟨r', hr'⟩ := (isUnit_of_notMem ho hρ hr).exists_left_inv
  obtain ⟨v, hv, -⟩ := existsUnique_isVecOver hψ.2.1.1 t
  obtain ⟨u₁, hu₁, -⟩ := existsUnique_isVecOver (pull_grp M.pK).1 u
  obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver (pull_grp M.pw).1 v
  have hu₁' : u₁.left ≫ prj M.pK = spMap (dualMap io) ≫ u.left := hu₁
  have hv₁' : v₁.left ≫ prj M.pw = spMap (dualMap (algebraMap Tv.V Tv.Fr)) ≫ v.left := hv₁
  have hv' : v.left ≫ ψ = spMap (dualMap ρ) ≫ t.left := hv
  have hrt' : (sc ((r : K₁) * cl) ≫ u).left ≫ s.φB = spMap (dualMap (algebraMap (𝓞 K₁) K₁)) ≫ t.left := hrt
  have hring : (algebraMap Tv.V Tv.Fr).comp ρ = io.comp (algebraMap (𝓞 K₁) K₁) := RingHom.ext hρ
  have e₁ : v₁ = sc (io ((r : K₁) * cl)) ≫ u₁ := by
    refine Over.OverMorphism.ext (((pull_grp M.pw).1.paste_horiz hψ.2.1.1).hom_ext ?_
      ((Over.w _).trans (Over.w _).symm))
    show v₁.left ≫ prj M.pw ≫ ψ = (sc (io ((r : K₁) * cl)) ≫ u₁).left ≫ prj M.pw ≫ ψ
    have a₁ : v₁.left ≫ prj M.pw ≫ ψ = spMap (dualMap ((algebraMap Tv.V Tv.Fr).comp ρ)) ≫ t.left := by
      rw [← Category.assoc, hv₁', Category.assoc, hv', ← Category.assoc, dual_comp]
    have a₂ : (sc (io ((r : K₁) * cl)) ≫ u₁).left ≫ prj M.pK ≫ s.φB =
        spMap (dualMap (io.comp (algebraMap (𝓞 K₁) K₁))) ≫ t.left := by
      rw [← Category.assoc, sc_over hu₁', Category.assoc, hrt', ← Category.assoc, dual_comp]
    rw [a₁, hsq, a₂, hring]
  have hn : (n' : K₁) ≠ 0 := Nat.cast_ne_zero.2 s.n_pos.ne'
  refine lift_through_split hK io.injective (IsFractionRing.injective Tv.V Tv.Fr) M.pK M.pw s.n_pos hτ.1 s.split he
    (isTangent_sc (hv.isTangent hψ.2.1 ht) r') hu₁' _ ?_
  have e₂ : io ((n' : K₁) * cl) * io (n' : K₁)⁻¹ = algebraMap Tv.V Tv.Fr r' * io ((r : K₁) * cl) := by
    rw [← map_mul, mul_right_comm, mul_inv_cancel₀ hn, _root_.one_mul, map_mul, ← hρ, ← _root_.mul_assoc, ← map_mul, hr',
      map_one, _root_.one_mul]
  rw [e₂, ← sc_mul, Category.assoc, ← e₁]
  exact sc_over hv₁' r'

end GlobalTheory.ArcCM
