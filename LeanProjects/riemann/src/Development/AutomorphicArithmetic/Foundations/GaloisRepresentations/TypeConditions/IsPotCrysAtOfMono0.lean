import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.OpenUnr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolCoeffZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullDegreeLabelForcesTrivialWildInertiaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsOfCgTrue

noncomputable section

namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.WeilDeligne

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def Gw {w : PlE H} (y : A.LP w) : Prop := A.unr y ∨ (thr w (A.lpDim y) = 2 ∧ Sep N A y)

variable {N A}
theorem Gw.nc (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {y : A.LP w} (h : Gw N A y) : Nc N A y :=
  h.elim Nc.of_unr fun k => nc_of_sep T k.1 k.2
end

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem NcW.congr {x y : WD h} (k : NcW x) (d : y.lpDim = x.lpDim) (m : x.mono0 → y.mono0)
    (e : ∀ σ ∈ Ine (F := E) B, y.inePol σ = x.inePol σ) : NcW y :=
  ⟨fun σ hσ => by rw [e σ (GlobalTheory.TameEig.wild_mem_Ine B σ hσ), d]; exact k.1 σ hσ, m k.2.1,
    fun γ hγ hc z hz => k.2.2 γ hγ hc z (by rwa [← e γ hγ, ← d])⟩

theorem NcW.char {x c : WD h} (k : NcW x) (hc : c.lpDim = 1) (hu : c.unr) : NcW (x.lpChar c) := by
  refine k.congr ?_ (WD.monomial_char_iff _ _ hc).2 fun σ hσ => ?_
  · obtain ⟨n, a, rfl⟩ := x.exists_rep
    obtain ⟨n', b, rfl⟩ := c.exists_rep
    rw [WD.lpDim_mk] at hc
    rw [WD.lpChar_mk, WD.lpDim_mk, WD.lpDim_mk, Module.finrank_tensorProduct, hc, mul_one]
  · rw [GlobalTheory.RowTieLP.inePol_char hc hσ (z := 1) (by rw [inePol_of_unr hu hσ, hc]; simp), scaleRoots_one]

theorem NcW.tw {x : WD h} (k : NcW x) (s : ℝ) : NcW (x.lpTw s) := by
  refine k.congr ?_ (WD.monomial_twist_iff _ _).2 fun σ hσ => ?_
  · obtain ⟨n, a, rfl⟩ := x.exists_rep
    rw [WD.lpTw_mk, WD.lpDim_mk, WD.lpDim_mk]
  · obtain ⟨n, a, rfl⟩ := x.exists_rep
    rw [WD.lpTw_mk, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.charPol_mk, WDRep.tw_ρ,
      deg_ineIncl]
    simp
end
end UpperTheory.GalS

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp

variable (D : D7) (T : WDTie D.nd D.naut) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))

def _root_.UpperTheory.GalS.IsGaloisRepOfN (D : D7) {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ w : PlE D.host, w ∉ placesOver D.host.E l →
    (UpperTheory.GalS.Gw D.nd D.naut (D.naut.locG π w) → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        D.naut.inePol (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) s) ∧
    (D.naut.unr (D.naut.locG π w) →
      (r '' (Ine (F := D.host.E) (D.nd.plOm.1 w) : Set (GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D))).Finite) ∧
    (D.naut.unr (D.naut.locG π w) → ∀ (B : ValuationSubring D.nd.Om) (s : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) s →
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))

structure IsAttachedAwayS : Prop where
  cont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))
  ss : IsSSRep r
  away : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
    UpperTheory.GalS.Aw (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hl ι r)
      (T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2)))
  temp : ∀ w : PlE D.host, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.unr (D.naut.locG π w) →
    ∀ α ∈ D.naut.frobEig (D.naut.locG π w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((a : ℝ) + 3) / 2)

structure IsAttachedHodgeS : Prop extends IsAttachedAwayS D T ι π s r where
  above : ∀ w ∈ placesOver D.host.E l, ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
    (UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) → IsDeRhamOf D ι π s r Bw) ∧
      (D.naut.unr (D.naut.locG π w) → IsCrysAt (D.loc l) Bw (resDec D.nd.plOm.1 r w)) ∧
      (UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) → IsPotCrysAt (D.loc l) Bw (resDec D.nd.plOm.1 r w))

def _root_.UpperTheory.GalS.GalHodge0 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r) (s : ℝ), D.naut.csd π → RegAlgShift D.naut π s →
    ∃ r, IsAttachedHodgeS D T ι π s r

def _root_.UpperTheory.GalS.GalHodgeN : Prop :=
  UpperTheory.GalS.GalHodge0 D T ∧ GlobalTheory.TypeLeaf.WildOne D ∧
  (∀ π : D.naut.CG D.R.r, D.naut.csd π → ∀ w w', IsConjPl D.host w w' →
    UpperTheory.GalS.Sep D.nd D.naut (D.naut.locG π w) → UpperTheory.GalS.Sep D.nd D.naut (D.naut.locG π w')) ∧
  ∀ (C₀ : Formalism.L2.Host.CharFrame D) (S : GlobalTheory.HeightCounting.CharSide D C₀) (π : D.naut.CG 1) (w : PlE D.host), (S.e1 π).1.TameAt w →
    UpperTheory.GalS.Tm D.nd D.naut (D.naut.locG π w)

variable {D T ι π s r}

theorem IsAttachedAwayS.frob (h : IsAttachedAwayS D T ι π s r) {w : PlE D.host}
    (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (hu : D.naut.unr (D.naut.locG π w)) :
    (∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), r σ = 1) ∧
    ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) σ →
      (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2))).map fun α => X - C α).prod := by
  have h1 := (D.naut.unr_tw _ (s + (1 - (a : ℝ)) / 2)).2 hu
  have e := (h.away w hl).eq_unr ((T.unr w _).1 h1)
  have h2 : (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hl ι r).unr := by rw [e, ← T.unr]; exact h1
  refine ⟨(GlobalTheory.WeilDeligne.unr_wdOf_iff hl ι h.cont).1 h2, fun B σ hB hσ => ?_⟩
  rw [GlobalTheory.WeilDeligne.frobEig_wdOf hl ι h.cont h2 hB hσ, e, T.frobEig w _ h1]

end GlobalTheory.TripleLocal

namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)

section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem exists_crystalline_galois_character (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hG : UpperTheory.GalS.CuspU)
    (ι : Qbar l ≃+* ℂ) (ψ : HChar E) (hu : ∀ v, ψ.UnrAt v) (hr : ∀ τ, ∃ n : ℤ, expo ψ τ = n)
    (hp : ∃ χ, IsPolarized ((CuspSub.triv E (le_refl 1)).twist ψ) χ) :
    ∃ c : G E Ω →* (Qbar l)ˣ, Continuous c ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (B : ValuationSubring Ω) (g : G E Ω),
        IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g → ι (c g : Qbar l) = (((ψ.val w)⁻¹ : ℂˣ) : ℂ)) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
        IsCrysAt P Bw ((GeneralLinearGroup.scalar (Fin 1)).comp (c.comp (Dec (F := E) A).subtype)) := by
  obtain ⟨χ, hχ⟩ := hp
  have hreg : (CG.mk ((CuspSub.triv E (le_refl 1)).twist ψ)).IsRegAlg := (CG.isRegAlg_ofChar ψ).2 hr
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι 1 le_rfl _ χ hreg hχ
  have hcr : Continuous fun g => (r g : Matrix (Fin 1) (Fin 1) (Qbar l)) := Units.continuous_val.comp H.cont
  have hsc : (GeneralLinearGroup.scalar (Fin 1)).comp (Matrix.GeneralLinearGroup.det.comp r) = r := by
    ext g i j
    rw [MonoidHom.comp_apply, coe_scalar, Subsingleton.elim i 0, Subsingleton.elim j 0]
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    change Matrix.det (r g : Matrix (Fin 1) (Fin 1) (Qbar l)) = _
    rw [Matrix.det_fin_one]
  have hdet : Continuous fun x : GL (Fin 1) (Qbar l) => Matrix.GeneralLinearGroup.det x := GeneralLinearGroup.continuous_det
  refine ⟨MonoidHom.comp Matrix.GeneralLinearGroup.det r, hdet.comp H.cont, fun w hl B g hB hg => ?_, fun P AI hT w A h O _ _ _ Bw hj => ?_⟩
  · obtain ⟨y1, y2⟩ := locPar_ofChar_unr hL ψ hB (hu w)
    have e1 : wdOf hB hl ι r = ParLaws.locPar hL (CG.ofChar ψ) hB := by
      rw [H.eq_locPar hL hF hl hB y1, show (1 - ((1 : ℕ) : ℝ)) / 2 = 0 by norm_num, WD.lpTw_zero]
      rfl
    have f := frobEig_wdOf hl ι hcr (e1 ▸ y1) hB hg
    rw [e1, y2] at f
    have h1 : (r g : Matrix (Fin 1) (Fin 1) (Qbar l)).charpoly = X - C ((r g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0) := by
      simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]
    rw [h1] at f
    have f2 := congrArg (fun p => p.coeff 0) f
    simp at f2
    change ι (Matrix.det _) = _
    rw [Matrix.det_fin_one]
    exact f2.trans (Units.val_inv_eq_inv_val _).symm
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E 1 ((CuspSub.triv E (le_refl 1)).twist ψ) w
    have hc := (H.above P AI hT w A h O Bw hj).crys σ hσ ((ParLaws.unr_iff (ParLaws.isRec_locRec hL h) (ParLaws.toRep σ)).1 (by
      rw [← ParLaws.locPar_mk hL hσ h]
      exact (locPar_ofChar_unr hL ψ h (hu w)).1))
    have e : (GeneralLinearGroup.scalar (Fin 1)).comp ((Matrix.GeneralLinearGroup.det.comp r).comp (Dec (F := E) A).subtype) =
        r.comp (Dec (F := E) A).subtype := by
      rw [← MonoidHom.comp_assoc, hsc]
    rw [e]
    exact hc

theorem potentially_crystalline_at_of_local_parameter (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : UpperTheory.GalS.CuspU) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : UpperTheory.GalS.CarU)
    (hD : ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite → Dense {g : G E Ω | ∃ w ∉ S, ∃ B : ValuationSubring Ω,
      IsPlaceOver (F := E) B w ∧ IsFrob (F := E) B (normV w) g})
    {π₀ : CuspSub E a} (ha : 2 ≤ a) (hc : π₀.IsCsd) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s)
    {ξ : HChar E} (hξu : ∀ v, ξ.UnrAt v) (hξc : (CG.ofChar ξ).IsCsd) (hξc' : (CG.ofChar ξ⁻¹).IsCsd)
    (hreg : (CG.mk (π₀.twist ξ)).IsRegAlg) (hint : ∀ τ, ∃ n : ℤ, expo (ξ⁻¹ * ν) τ = n)
    {ι : Qbar l ≃+* ℂ} {χ : HChar (maximalRealSubfield E)} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : UpperTheory.GalS.IsGalU (π₀.twist ν) χ ι r wt HT)
    {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E l)
    {A : ValuationSubring Ω} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
    (hm : UpperTheory.GalS.NcW (ParLaws.locPar hL (CG.mk π₀) h)) :
    IsPotCrysAt P Bw (r.comp (Dec (F := E) A).subtype) := by
  have hc' : (π₀.twist ξ).IsCsd := CG.IsCsd.twist hξc (π := CG.mk π₀) hc
  obtain ⟨r₀, wt₀, HT₀, H₀, K₀⟩ := hGL E Ω l ι a ha _ hc' hreg
  have e0 : (π₀.twist ξ).twist (ξ⁻¹ * ν) = π₀.twist ν := by
    rw [← CuspSub.twist_mul, mul_inv_cancel_left]
  have hψu : ∀ v, (ξ⁻¹ * ν).UnrAt v := fun v => (hξu v).inv.mul (hν.1 v)
  have hp : ∃ χ', IsPolarized ((CuspSub.triv E (le_refl 1)).twist (ξ⁻¹ * ν)) χ' := by
    rw [CuspSub.twist_mul]
    exact isPolarized_twist hξc' hν
  obtain ⟨c, hcc, hcf, hcr⟩ := exists_crystalline_galois_character (Ω := Ω) hL hF hG ι (ξ⁻¹ * ν) hψu hint hp
  have hc0 : Continuous fun g => (r₀ g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H₀.cont
  have hc1 : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H.cont
  have hc2 : Continuous fun g => (twistBy c r₀ g : Matrix (Fin a) (Fin a) (Qbar l)) := by
    simp only [coe_twistBy]
    exact (Units.continuous_val.comp hcc).smul hc0
  obtain ⟨B, hBc⟩ := conj_of_frob hD hc1 hc2 H.ss (isSSRep_twistBy c H₀.ss) (by
    filter_upwards [eventually_natCast_notMem E l, ParLaws.eventually_unr (Ω := Ω) hL hF (CG.mk (π₀.twist ξ))] with w hl hu Bp g hBp hg
    have e3 : ParLaws.locPar hL (CG.mk (π₀.twist ν)) hBp =
        (ParLaws.locPar hL (CG.mk (π₀.twist ξ)) hBp).lpChar (ParLaws.locPar hL (CG.ofChar (ξ⁻¹ * ν)) hBp) := by
      rw [← e0]
      exact ParLaws.locPar_twist hL hF (CG.mk (π₀.twist ξ)) _ hBp
    obtain ⟨y1, y2⟩ := locPar_ofChar_unr hL (ξ⁻¹ * ν) hBp (hψu w)
    have u1 := hu _ hBp
    have e1 := H.eq_locPar hL hF hl hBp (by rw [e3]; exact WD.unr_lpChar _ _ u1 y1)
    have e2 := H₀.eq_locPar hL hF hl hBp u1
    have u2 : (wdOf hBp hl ι r).unr := by rw [e1, e3, WD.unr_tw]; exact WD.unr_lpChar _ _ u1 y1
    have u3 : (wdOf hBp hl ι r₀).unr := by rw [e2, WD.unr_tw]; exact u1
    have f1 := frobEig_wdOf hl ι hc1 u2 hBp hg
    have f2 := frobEig_wdOf hl ι hc0 u3 hBp hg
    rw [e1, e3, WD.frobEig_tw _ _ (WD.unr_lpChar _ _ u1 y1), WD.frobEig_char _ _ _ u1 y1 y2] at f1
    rw [e2, WD.frobEig_tw _ _ u1] at f2
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [f1, coe_twistBy]
    have f3 : (((c g : Qbar l) • (r₀ g : Matrix (Fin a) (Fin a) (Qbar l))).charpoly.map ι.toRingHom) =
        ((ι (c g : Qbar l)) • ((r₀ g : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom)).charpoly := by
      rw [← Matrix.charpoly_map]
      congr 1
      ext i j
      simp
    rw [f3, GlobalTheory.Triple.charpoly_smul_of_prod _ _ _ (by rw [Matrix.charpoly_map]; exact f2), hcf w hl Bp g hBp hg]
    simp only [Multiset.map_map, Function.comp_def]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    congr 2
    ring)
  obtain ⟨σ₁, hσ₁, -⟩ := LocEx.exists_isLocComp hF E a (π₀.twist ξ) w
  have g2 : ParLaws.locRec hL h (algNorm σ₁) =
      (ParLaws.locPar hL (CG.mk (π₀.twist ξ)) h).lpTw ((1 - (a : ℝ)) / 2) := by
    rw [rec_algNorm (ParLaws.isRec_locRec hL h) σ₁]
    exact congrArg (fun x : WD h => x.lpTw _) (ParLaws.locPar_mk hL hσ₁ h).symm
  have hn : UpperTheory.GalS.NcW ((ParLaws.locPar hL (CG.mk (π₀.twist ξ)) h).lpTw ((1 - (a : ℝ)) / 2)) := by
    have e4 : ParLaws.locPar hL (CG.mk (π₀.twist ξ)) h =
        (ParLaws.locPar hL (CG.mk π₀) h).lpChar (ParLaws.locPar hL (CG.ofChar ξ) h) :=
      ParLaws.locPar_twist hL hF (CG.mk π₀) ξ h
    rw [e4]
    exact (hm.char (ParLaws.lpDim_locPar hL _ h) (locPar_ofChar_unr hL ξ h (hξu w)).1).tw _
  have g1 := K₀ P AI ⟨T⟩ w hw A h O Bw hj σ₁ hσ₁ _ (ParLaws.isRec_locRec hL h) (g2 ▸ hn)
  have hm' : (wdAt P ι Bw h hj (r₀.comp (Dec (F := E) A).subtype)).mono0 := g1.mono (g2 ▸ hn.2.1)
  have hab := H₀.above P AI ⟨T⟩ w A h O Bw hj
  have hpst := hB.isPstAt T Bw (r₀.comp (Dec (F := E) A).subtype) (H₀.cont.comp continuous_subtype_val |> Units.continuous_val.comp)
    (hab.deRham (UpperTheory.GalS.nice_of_locPar hL hF h hn))
  have hpot := (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj P ι _ hpst).1 hm'
  have hpot2 := potCrys_twistBy T Bw (c.comp (Dec (F := E) A).subtype) (r₀.comp (Dec (F := E) A).subtype) hpot
    (hcr P AI ⟨T⟩ w A h O Bw hj)
  refine (GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ (r.comp (Dec (F := E) A).subtype) B⁻¹ (fun g => ?_)).2.2.1 hpot2
  have := hBc g
  change r g = B⁻¹ * twistBy c r₀ g * B⁻¹⁻¹
  rw [this]
  group

end G

theorem galHodge_of_cgTrue_alt (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : UpperTheory.GalS.CuspU) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : UpperTheory.GalS.CarU)
    {D : D7} {T : WDTie D.nd D.naut} (C : CGTrue hL D T) : UpperTheory.GalS.GalHodge0 D T := by
  intro l _ ι π s hc hr
  have := host_isCMField D.host
  have ha : 2 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (C.e _ π).1
  have hmk : CG.mk π₀ = (C.e _ π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (C.csd _ π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E s
  set ν := GlobalTheory.HeckeGal.Model.absPow D.host.E s
  have inf₁ : ∀ τ, (CG.mk (π₀.twist ν)).infChar τ = (D.naut.infG π τ).map (· + (s : ℂ)) := fun τ => by
    have h1 := (ParLaws.hasInfChar_infChar (CG.mk π₀) τ).twist ν
    rw [(GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ] at h1
    rw [C.inf, CGu.infChar, ← hmk]
    exact h1.infChar_eq
  have hreg : (CG.mk (π₀.twist ν)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    obtain ⟨h1, h2⟩ := hr τ
    rw [inf₁]
    refine ⟨h1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    exact h2 y hy
  obtain ⟨ψp, hP⟩ := isPolarized_twist hc₀ hν
  obtain ⟨r, wt, HT, H⟩ := hG _ D.nd.Om l ι _ (by omega) _ ψp hreg hP
  have hloc : ∀ (w : PlE D.host) (u : ℝ), T.e w (D.naut.lpTw (D.naut.locG π w) u) =
      (ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [T.tw, C.loc, hmk]
    rfl
  have haway : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      UpperTheory.GalS.Aw (wdOf (D.nd.plOm.2 w) hl ι r) (T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (D.R.r : ℝ)) / 2))) := fun w hl => by
    have e := locPar_twist_abs hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    have k := H.aw_locPar hL hF hl (D.nd.plOm.2 w)
    rw [show ParLaws.locPar hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, WD.lpTw_add, ← hloc] at k
    exact k
  have hv : s + (1 - (D.R.r : ℝ)) / 2 + (wt : ℝ) / 2 = 0 := by
    have hm : ∀ τ, π₀.HasInfChar τ ((CG.mk π₀).infChar τ) := fun τ => ParLaws.hasInfChar_infChar (CG.mk π₀) τ
    have hw := GlobalTheory.TempSatGal.weight_eq_rank_sub_one_sub_two_mul_of_inf_char_shift (by omega) H (fun τ => (CG.mk π₀).infChar τ) s (fun τ => (hm τ).1)
      (fun τ => by rw [inf₁, C.inf, CGu.infChar, ← hmk])
      (fun τ => GlobalTheory.CsdTwistGal.infChar_conj_of_isCsd _ _ π₀ hc₀ τ _ _ (hm τ) (hm _))
    rw [hw]; ring
  have htemp : ∀ w : PlE D.host, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.unr (D.naut.locG π w) →
      ∀ α ∈ D.naut.frobEig (D.naut.locG π w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((D.R.r : ℝ) + 3) / 2) := fun w hl hu α hα => by
    obtain ⟨-, hU, hS⟩ := GlobalTheory.HeightCounting.Blocks.readsCusp hF C
    obtain ⟨B, hB, e⟩ := hS _ π w (by omega) hu
    rw [e] at hα
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hα
    have k : UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) (b : ℂ) :=
      PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound D.host.E _ _ (hU _ π (by omega)) w B hB b hb
    rw [Units.val_inv_eq_inv_val]
    have hq := UpperTheory.GalN.one_lt_q (H := D.host) w
    refine (k.inv hq).2.le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq.le) ?_)
    have : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
    linarith
  refine ⟨r, ⟨Units.continuous_val.comp H.cont, H.ss, haway, htemp⟩, fun w hw O _ _ _ Bw hj => ?_⟩
  have hpar : T.e w (D.naut.locG π w) = ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w) := by
    rw [C.loc, hmk]
    rfl
  have hab := H.above (D.loc l) (D.locA l) ⟨D.locT l⟩ w _ (D.nd.plOm.2 w) O Bw hj
  have hN : UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) → UpperTheory.GalS.Nice (π₀.twist ν) (D.nd.plOm.2 w) := fun k => by
    refine UpperTheory.GalS.nice_of_locPar hL hF _ (UpperTheory.GalS.NcW.tw ?_ _)
    have e := locPar_twist_abs hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    rw [show ParLaws.locPar hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, ← hpar]
    exact (UpperTheory.GalS.ncW_of_nc T k).tw _
  refine ⟨fun k => ⟨hab.deRham (hN k), fun τ L τ' hτ => ⟨HT τ, ?_, hab.jumps (hN k) τ L τ' hτ⟩⟩, fun hu => ?_, fun hm => ?_⟩
  · rw [H.weights, inf₁, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    ring
  · obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hF _ _ (π₀.twist ν) w
    refine hab.crys σ₀ hσ₀ ((ParLaws.unr_iff (ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) (ParLaws.toRep σ₀)).1 ?_)
    rw [← ParLaws.locPar_mk hL hσ₀ (D.nd.plOm.2 w)]
    have e := locPar_twist_abs hL hF (CG.mk π₀) hν (D.nd.plOm.2 w)
    rw [show ParLaws.locPar hL (CG.mk (π₀.twist ν)) (D.nd.plOm.2 w) = _ from e, WD.unr_tw, ← hpar]
    exact (T.unr w _).1 hu
  · have hm' : UpperTheory.GalS.NcW (ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w)) := by
      rw [← hpar]
      exact UpperTheory.GalS.ncW_of_nc T hm
    have hs2 : 2 * s = ((D.R.r : ℤ) - 1 - wt : ℤ) := by
      push_cast
      linarith
    have key : ∀ ξ : HChar D.host.E, (∀ τ, ∃ n : ℤ, expo ξ τ = (s : ℂ) + n) →
        (CG.mk (π₀.twist ξ)).IsRegAlg ∧ ∀ τ, ∃ n : ℤ, expo (ξ⁻¹ * ν) τ = n := fun ξ hξ => by
      refine ⟨(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, fun τ => ?_⟩
      · obtain ⟨h1, h2⟩ := hr τ
        obtain ⟨n, hn⟩ := hξ τ
        have e := ((ParLaws.hasInfChar_infChar (CG.mk π₀) τ).twist ξ).infChar_eq
        have e' : (CG.mk (π₀.twist ξ)).infChar τ = (D.naut.infG π τ).map (· + expo ξ τ) := by
          rw [C.inf, CGu.infChar, ← hmk]
          exact e
        rw [e']
        refine ⟨h1.map (add_left_injective _), fun z hz => ?_⟩
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
        obtain ⟨m, hm2⟩ := h2 y hy
        refine ⟨m + n, ?_⟩
        simp only [hn]
        push_cast
        linear_combination hm2
      · obtain ⟨n, hn⟩ := hξ τ
        refine ⟨-n, ?_⟩
        rw [expo_mul, expo_inv, hn, (GlobalTheory.T.heckeChar_exponent_of_infinityType _ ν).2.1 s hν τ]
        push_cast
        ring
    have hD : ∀ S : Set (HeightOneSpectrum (𝓞 D.host.E)), S.Finite → Dense {g : G D.host.E D.nd.Om | ∃ w ∉ S,
        ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) g} := fun S hS =>
      Dense.mono (by rintro g ⟨w, h1, -, h2⟩; exact ⟨w, h1, h2⟩)
        (GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 GlobalTheory.Published.chebotarevDegreeOne') S hS)
    obtain ⟨ξh, x1, x2, x3, x4⟩ := exists_halfChar D
    have hone : ∀ v, (1 : HChar D.host.E).UnrAt v := fun v x _ => rfl
    have cone : (CG.ofChar (1 : HChar D.host.E)).IsCsd := isCsd_ofChar_of_res _ _ (Or.inl
      ⟨fun v k => by
        simp only [HChar.resFin, MonoidHom.finset_prod_apply]
        exact Finset.prod_eq_one fun _ _ => rfl,
      fun v k => by
        simp only [HChar.resInf, MonoidHom.finset_prod_apply]
        exact Finset.prod_eq_one fun _ _ => rfl⟩)
    rcases Int.even_or_odd' ((D.R.r : ℤ) - 1 - wt) with ⟨k, hk | hk⟩
    · have hsk : (s : ℂ) = k := by
        rw [hk] at hs2
        push_cast at hs2
        have : s = k := by linarith
        rw [this]
        simp
      obtain ⟨k1, k2⟩ := key 1 fun τ => ⟨-k, by rw [CG.expo_one, hsk]; push_cast; ring⟩
      exact potentially_crystalline_at_of_local_parameter hL hF hG hB hGL hD ha hc₀ hν (fun v => hone v) cone (by rwa [inv_one]) k1 k2 H (D.locT l) hw
        (D.nd.plOm.2 w) Bw hj hm'
    · have hsk : (s : ℂ) = k + 1 / 2 := by
        rw [hk] at hs2
        push_cast at hs2
        have : s = k + 1 / 2 := by linarith
        rw [this]
        simp
      obtain ⟨k1, k2⟩ := key ξh fun τ => by
        obtain ⟨n, hn⟩ := x4 τ
        exact ⟨n - k, by rw [hn, hsk]; push_cast; ring⟩
      exact potentially_crystalline_at_of_local_parameter hL hF hG hB hGL hD ha hc₀ hν x1 x2 x3 k1 k2 H (D.locT l) hw (D.nd.plOm.2 w) Bw hj hm'

def _root_.UpperTheory.GalS.GaloisRepsN (D : D7) : Prop :=
  ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ r, UpperTheory.GalS.IsGaloisRepOfN D π l ι r

theorem _root_.UpperTheory.GalS.ghOf (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : GlobalTheory.GalOfCusp.LocalGlobalAboveL)
    (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (C : CGTrue hL D T) (_ : LabTrue D T) : GalHodge D T :=
  (GlobalTheory.T.galois_hodge_of_cuspidal hL hF hG hB hGL D T C).1

theorem _root_.UpperTheory.GalS.ghOf' (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : UpperTheory.GalS.CuspU) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : UpperTheory.GalS.CarU)
    (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (C : CGTrue hL D T) (hl : LabTrue D T) : UpperTheory.GalS.GalHodgeN D T :=
  ⟨galHodge_of_cgTrue_alt hL hF hG hB hGL C, GlobalTheory.T.full_degree_label_forces_trivial_wild_inertia D T hl, fun π hc _ _ hw k => UpperTheory.GalS.sep_conj hL hF C π hc hw k,
    fun _ S π w ht => UpperTheory.GalS.tm_rankOne hL C S π w ht⟩

end GlobalTheory.HodgeOfTrue

namespace GlobalTheory.GalAway
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeightCounting

theorem galoisReps_of_cgTrue_alt : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL → UpperTheory.GalS.CuspU → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.HeightCounting.CGTrue hL D T → UpperTheory.GalS.GaloisRepsN D := by
  intro hL hF hG D T C π hc hr l _ ι
  have := host_isCMField D.host
  have ha : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hr' : (C.e _ π).1.IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [C.inf] at this
  obtain ⟨r, h1, h2, h3⟩ := UpperTheory.GalS.exists_aw hL hF hG D.nd.Om ι ha (C.e _ π).1 ((C.csd _ π).1 hc) hr'
  refine ⟨r, h1, h2, fun w hw => ?_⟩
  have hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hw
  have k : UpperTheory.GalS.Aw (wdOf (D.nd.plOm.2 w) hl ι r) (T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))) := by
    rw [T.tw, C.loc]
    exact h3 w hl _ _
  refine ⟨fun hg s hs => ?_, fun hu => ?_, fun hu B s hB hs => ?_⟩
  · rw [T.inePol w _ s hs, inePol_wdOf (h := D.nd.plOm.2 w) hl ι h1 hs, WD.inePol_of_mem_Ine _ hs, WD.inePol_of_mem_Ine _ hs,
      k.ine (UpperTheory.GalS.ncW_of_nc T ((UpperTheory.GalS.nc_tw _ _).2 (hg.nc T))) _ (deg_ineIncl _)]
  · rw [← weilDeligneParam_monodromy_eq_zero_iff hl ι h1]
    exact k.mono (UpperTheory.GalS.ncW_of_nc T ((UpperTheory.GalS.nc_tw _ _).2 (.of_unr hu)))
  · have hu' := (D.naut.unr_tw _ ((1 - (D.R.r : ℝ)) / 2)).2 hu
    have e := (k.eq_unr ((T.unr w _).1 hu')).symm
    rw [galPol, T.frobEig w _ hu', e]
    exact frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hs

end GlobalTheory.GalAway
