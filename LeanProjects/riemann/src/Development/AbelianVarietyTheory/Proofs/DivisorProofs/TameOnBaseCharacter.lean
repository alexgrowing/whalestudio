import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCharacterOnLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceOverTypePrimeDividesOrConjugate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MuLift

section Ring

theorem orth_mul {R : Type} [CommRing R] {e f : R} (he : e * e = e) (hf : f * f = f) (hef : e * f = 0)
    {p q p' q' : R} (hp : p * p' = 1) (hq : q * q' = 1) :
    (e * p + f * q + (1 - e - f)) * (e * p' + f * q' + (1 - e - f)) = 1 := by
  have eg : e * (1 - e - f) = 0 := by linear_combination -he - hef
  have fg : f * (1 - e - f) = 0 := by linear_combination -hf - hef
  have gg : (1 - e - f) * (1 - e - f) = 1 - e - f := by linear_combination -eg - fg
  linear_combination (p * p') * he + (q * q') * hf + (p * q' + q * p') * hef + (p + p') * eg + (q + q') * fg + gg +
    e * hp + f * hq

theorem exists_root {R A : Type} [CommRing R] [CommRing A] (c : R →+* R) (hc : ∀ z, c (c z) = z) (S : Subring R)
    (hS : ∀ z ∈ S, c z ∈ S) (p : R →+* A) {e d : R} (he : e * e = e) (hef : e * c e = 0) (heS : e ∈ S)
    (hpe : p e = 0) (hpf : p (c e) = 0) (x : Rˣ) (hx : (x : R) = d * c x) (h1 : p x = 1) (h2 : (x : R) ∈ S)
    (h3 : ((x⁻¹ : Rˣ) : R) ∈ S) :
    ∃ y : Rˣ, (y : R) = d * c y ∧ p y = 1 ∧ (y : R) ∈ S ∧ ((y⁻¹ : Rˣ) : R) ∈ S ∧ c e * y = c e ∧ e * y = e * d := by
  have hf : c e * c e = c e := by rw [← map_mul, he]
  have hxx : ((x⁻¹ : Rˣ) : R) * x = 1 := x.inv_mul
  have hcx : c ((x⁻¹ : Rˣ) : R) * c x = 1 := by rw [← map_mul, hxx, map_one]
  have hw := orth_mul he hf hef hcx hxx
  let w : Rˣ := ⟨_, _, hw, (mul_comm _ _).trans hw⟩
  have hw1 : (w : R) = e * c ((x⁻¹ : Rˣ) : R) + c e * ((x⁻¹ : Rˣ) : R) + (1 - e - c e) := rfl
  have hw2 : ((w⁻¹ : Rˣ) : R) = e * c (x : R) + c e * (x : R) + (1 - e - c e) := rfl
  have hcw : c w = w := by
    rw [hw1]
    simp only [map_add, map_mul, map_sub, map_one, hc]
    ring
  have hm : ∀ a ∈ S, e * c a + c e * a + (1 - e - c e) ∈ S := fun a ha =>
    add_mem (add_mem (mul_mem heS (hS _ ha)) (mul_mem (hS _ heS) ha)) (sub_mem (sub_mem (one_mem _) heS) (hS _ heS))
  refine ⟨x * w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hcw, ← mul_assoc, ← hx]
  · rw [Units.val_mul, hw1]
    simp only [map_add, map_mul, map_sub, map_one, h1, hpe, hpf]
    ring
  · rw [Units.val_mul, hw1]
    exact mul_mem h2 (hm _ h3)
  · rw [mul_inv, Units.val_mul, hw2]
    exact mul_mem h3 (hm _ h2)
  · rw [Units.val_mul, hw1]
    linear_combination (x * c ((x⁻¹ : Rˣ) : R) - x) * hef + (x * ((x⁻¹ : Rˣ) : R) - x) * hf + c e * hxx
  · rw [Units.val_mul, hw1]
    linear_combination (x * c ((x⁻¹ : Rˣ) : R) - x) * he + (x * ((x⁻¹ : Rˣ) : R) - x) * hef +
      e * c ((x⁻¹ : Rˣ) : R) * hx + e * d * hcx

end Ring

section General

open NumberField Formalism.L2.DIV
open scoped TensorProduct

theorem det_restricted_block {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (h : n = r) (g : GL (Fin n) κ) :
    Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) = Matrix.GeneralLinearGroup.det g := by
  subst h
  have hg : g ∈ blockTri (blk2 n) := fun i j hij => by
    simp [blk2] at hij
  congr 1
  exact Units.ext (upper_block_val_submatrix hr hg)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem resS_eq_gen (PP : Pl E) {a x y : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    (hx : x ∈ Formalism.L2.Herm.intAf F E) (hy : y ∈ Formalism.L2.Herm.intAf F E) (h1 : resS F PP ⟨a, ha⟩ = 1)
    (h : a * x = a * y) : resS F PP ⟨x, hx⟩ = resS F PP ⟨y, hy⟩ := by
  have e : (⟨a, ha⟩ : Formalism.L2.Herm.intAf F E) * ⟨x, hx⟩ = ⟨a, ha⟩ * ⟨y, hy⟩ := Subtype.ext h
  have := congrArg (resS F PP) e
  rwa [map_mul, map_mul, h1, one_mul, one_mul] at this

theorem det_int_gen {n : ℕ} {β g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hg : g ∈ St β)
    {d : E ⊗[F] Formalism.L2.Herm.Af F} (hd : d = g.val.det) :
    ∃ h : d ∈ Formalism.L2.Herm.intAf F E, ∀ PP : Pl E,
      ((Matrix.GeneralLinearGroup.det (redFn β PP g) : (kP PP)ˣ) : kP PP) = resS F PP ⟨d, h⟩ := by
  obtain ⟨y, rfl⟩ := hg
  have h3 : d = (y.val.det : Formalism.L2.Herm.intAf F E) := by
    rw [hd]
    change (β * intGL _ _ _ y * β⁻¹).val.det = _
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    exact ((Formalism.L2.Herm.intAf F E).subtype.map_det y.val).symm
  subst h3
  refine ⟨y.val.det.2, fun PP => ?_⟩
  rw [redFn_frGL]
  exact ((resS F PP).map_det y.val).symm

end General

section Adelic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_idemSum (P : Finset (Pl D.host.E)) (h : ∀ Q ∈ P, ∀ Q' ∈ P, ¬ IsConjPl Q Q') :
    ∃ e : AE D, IsIdemSum e P :=
  GlobalTheory.GridIdem.exists_isIdemSum P (fun Q hQ => GlobalTheory.ParahoricLift.exists_isIdemAt (h Q hQ Q hQ))
    fun Q hQ Q' hQ' e => (GlobalTheory.IdemSupport.eq_or_eq_cP e).resolve_right fun e' =>
      h Q' hQ' Q hQ ((GlobalTheory.IdemSupport.isConjPl_iff Q' Q).2 e')

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a x => exact congrArg (a ⊗ₜ[D.host.F] ·) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

set_option maxHeartbeats 1000000 in

theorem mu_eq_prod {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (hV : MuVal V χ mu) {e : AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (hχ : TameOn χ e P c)
    {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {k : GA D V} (hf : k ∈ GfC V) (hk : finE V k ∈ St β) :
    mu k = ∏ PP ∈ P, ((c PP (Matrix.GeneralLinearGroup.det (redFn β PP (finE V k))) : ℂˣ) : ℂ) := by
  obtain ⟨hd, hr⟩ : ∃ h : toEAf D (Formalism.L2.Theta.mt V k).det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      ∀ PP : Pl D.host.E, ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V k)) : (kP PP)ˣ) : kP PP) =
        resS D.host.F PP ⟨_, h⟩ := det_int_gen hk ((toEAf D).map_det _)
  have e5 : (finHom V k).1.det = finPart D (Formalism.L2.Theta.mt V k).det := ((finPart D).map_det _).symm
  obtain ⟨x, hx, hx1, hx2, hx3⟩ := GlobalTheory.GeoLevel.LiftChar.exists_finUnit_root V k hf
    (e5 ▸ GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hd)
  obtain ⟨hei, her⟩ := GlobalTheory.TameProd.resS_idemSum he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨y, hy, hy1, hy2, hy3, hy4, hy5⟩ := exists_root (cA D) cA_cA
    ((Formalism.L2.Herm.intAf D.host.F D.host.E).comap (toEAf D))
    (fun z hz => GlobalTheory.IdemRes.toEAf_mem_of_finPart
      (GlobalTheory.IdemSupport.finPart_cA_mem (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hz)))
    (infPart D) (d := (Formalism.L2.Theta.mt V k).det) (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hei hinf
    (GlobalTheory.PlaceDatum.infPart_cA hinf) x hx hx1 (GlobalTheory.IdemRes.toEAf_mem_of_finPart hx2)
    (GlobalTheory.IdemRes.toEAf_mem_of_finPart hx3)
  rw [hV.2 k y hy]
  refine hχ y hy1 hy2 hy3 hy4 (fun PP => Matrix.GeneralLinearGroup.det (redFn β PP (finE V k))) fun PP hP => ?_
  refine (hr PP).trans (resS_eq_gen PP hei hd hy2 (her PP hP) ?_)
  rw [← RingHom.map_mul, ← hy5, RingHom.map_mul]

theorem tame_on_base_character {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (j : Fin D.R.m) {e : AE D}
    (he : IsIdemSum e L.Pg) : TameOn (L.mu0 ((j : ℕ) + 1)) e L.Pg fun PP => (L.chi ((j : ℕ) + 1) PP)⁻¹ := by
  have hM := L.C.isMu0 j
  refine GlobalTheory.TameProd.tameOn_of_tame D _ (L.C.mu0 j) e L.Pg _ (hL.mu0 j) hM.tame he ?_ (hL.chi j)
  intro PP h1 h2
  refine hM.unr PP fun k hk => ?_
  rcases GlobalTheory.StepLaw.div_or_isConjPl_div D L.C.P k PP hk with h | ⟨PP', h, hc⟩
  · exact h1 ((hL.Pg PP).2 ⟨k, h⟩)
  · exact h2 ⟨PP', (hL.Pg PP').2 ⟨k, h⟩, hc⟩

end Adelic

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem chiDet_mul_mu_eq_one : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A Ks) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → ∀ mu : GA D (Formalism.IndefR.Links.Wc D i) → ℂ, MuVal (Formalism.IndefR.Links.Wc D i) (R.mu0 ((i : ℕ) + 1)) mu → ∀ (g : G) (k : GA D (Formalism.IndefR.Links.Wc D i)), Formalism.IndefR.Lev.IsLevelLift (Formalism.IndefR.Links.Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → (∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ)) * mu k = 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i hL mu hV g k hk
  obtain ⟨hf, hp, hr⟩ := hk
  obtain ⟨e, he⟩ := exists_idemSum R.Pg (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hL.Pg)
  have hrk : (Formalism.IndefR.Links.Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  rw [mu_eq_prod hV he (tame_on_base_character hL i he) hf (Formalism.L2.DIV.parLev_St hp), ← Finset.prod_coe_sort R.Pg,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun PP _ => ?_
  have h1 : Matrix.GeneralLinearGroup.det (R.eG g PP) = Matrix.GeneralLinearGroup.det
      (Formalism.L2.DIV.redFn (R.βW i) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Wc D i) k)) :=
    (congrArg Matrix.GeneralLinearGroup.det (congrFun hr PP)).symm.trans
      (det_restricted_block (Formalism.IndefR.Links.r_le_rank_Wc i) hrk _)
  rw [h1, MonoidHom.inv_apply, Units.mul_inv]

end GlobalTheory.MuLift

end
