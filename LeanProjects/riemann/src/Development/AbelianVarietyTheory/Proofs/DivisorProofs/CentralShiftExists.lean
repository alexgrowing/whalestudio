import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveOfIndep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralShift

section Generic

variable {A : Type} [CommRing A] {n : ℕ}

theorem glued_idempotent_units_mul_eq_one {e e' a ai b bi : A} (h1 : e * e = e) (h2 : e * e' = 0) (h3 : e' * e' = e') (ha : a * ai = 1)
    (hb : b * bi = 1) : (e * a + e' * bi + (1 - e - e')) * (e' * b + e * ai + (1 - e - e')) = 1 := by
  linear_combination (a * ai - a - ai + 1) * h1 + (a * b + bi * ai - a - bi - b - ai + 2) * h2 +
    (bi * b - bi - b + 1) * h3 + e * ha + e' * hb

def scal (n : ℕ) {u v : A} (h : u * v = 1) : GL (Fin n) A where
  val := u • (1 : Matrix (Fin n) (Fin n) A)
  inv := v • (1 : Matrix (Fin n) (Fin n) A)
  val_inv := by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, one_smul, one_mul]
  inv_val := by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm v, h, one_smul, one_mul]

theorem scal_mem (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) {u : A} (h : u * σ u = 1) :
    scal n h ∈ Formalism.UG.UJ σ J := by
  change Formalism.UG.cT σ (u • (1 : Matrix (Fin n) (Fin n) A)) * J * (u • (1 : Matrix (Fin n) (Fin n) A)) = J
  have h1 : Formalism.UG.cT σ (u • (1 : Matrix (Fin n) (Fin n) A)) = σ u • Formalism.UG.cT σ (1 : Matrix (Fin n) (Fin n) A) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [h1, Formalism.UG.cT_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, h, one_smul, one_mul, mul_one]

theorem map_smul_one {B : Type} [CommRing B] (f : A →+* B) (u : A) :
    (u • (1 : Matrix (Fin n) (Fin n) A)).map f = f u • (1 : Matrix (Fin n) (Fin n) B) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem smul_one_comm (u : A) (M : Matrix (Fin n) (Fin n) A) :
    M * (u • (1 : Matrix (Fin n) (Fin n) A)) = (u • (1 : Matrix (Fin n) (Fin n) A)) * M := by
  rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

theorem smul_one_supp {f u : A} (h : f * (u - 1) = u - 1) (i j : Fin n) :
    f * (u • (1 : Matrix (Fin n) (Fin n) A) - 1) i j = (u • (1 : Matrix (Fin n) (Fin n) A) - 1) i j := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_one, h]
  · simp

theorem blockTri_of_scalar (b : Fin n → ℕ) {g : GL (Fin n) A} {u : A} (h : g.1 = u • (1 : Matrix (Fin n) (Fin n) A)) :
    g ∈ blockTri b := by
  intro i j hij
  show g.1 i j = 0
  have : i ≠ j := by
    rintro rfl
    exact lt_irrefl _ hij
  rw [h, Matrix.smul_apply, Matrix.one_apply_ne this, smul_zero]

theorem blockRestriction_of_scalar_eq_scalar {r : ℕ} (hr : r ≤ n) {g : GL (Fin n) A} {u : A} (h : g.1 = u • (1 : Matrix (Fin n) (Fin n) A))
    {k : GL (Fin r) A} (hk : k.1 = u • (1 : Matrix (Fin r) (Fin r) A)) : upperLeftBlock hr g = k := by
  apply Units.ext
  rw [upper_block_val_submatrix hr (blockTri_of_scalar _ h), h, hk]
  ext i j
  simp [Matrix.one_apply]

theorem scalar_of_center {ι : Type} {κ : ι → Type} [∀ i, CommRing (κ i)] {r : ℕ} {g : ∀ i, GL (Fin r) (κ i)}
    (hg : ∀ x, x * g = g * x) (i : ι) : ∃ u : (κ i)ˣ, (g i).1 = (u : κ i) • (1 : Matrix (Fin r) (Fin r) (κ i)) := by
  classical
  have h : g i ∈ Subgroup.center (GL (Fin r) (κ i)) := Subgroup.mem_center_iff.2 fun x => by
    have := congrFun (hg (Function.update 1 i x)) i
    simpa using this
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  rw [← hu]
  exact (Matrix.smul_one_eq_diagonal _).symm

end Generic

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem scalar_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {u v : Formalism.L2.Herm.intAf F E} (h : u * v = 1)
    {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x.1 = (u : E ⊗[F] Formalism.L2.Herm.Af F) • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    x ∈ St β ∧ ∀ P, (redFn β P x).1 = resS F P u • (1 : Matrix (Fin n) (Fin n) (kP P)) := by
  have e : frGL β (scal n h) = x := by
    apply Units.ext
    have e1 : ((frGL β (scal n h) : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      β.1 * (u • (1 : Matrix (Fin n) (Fin n) _)).map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 := rfl
    rw [e1, map_smul_one, smul_one_comm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hx]
    rfl
  subst e
  refine ⟨⟨_, rfl⟩, fun P => ?_⟩
  rw [redFn_frGL]
  exact map_smul_one (resS F P) u

theorem exists_int_res (S : Finset (Pl E)) (c : ∀ P : S, (kP P.1)ˣ) :
    ∃ a : 𝓞 E, a ≠ 0 ∧ ∀ P : S, Ideal.Quotient.mk P.1.asIdeal a = (c P : kP P.1) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨Q, hQ⟩
  · exact ⟨1, one_ne_zero, fun P => absurd P.2 (Finset.notMem_empty _)⟩
  choose x hx using fun P : S => Ideal.Quotient.mk_surjective (I := P.1.asIdeal) (c P : kP P.1)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun P => P.asIdeal) (fun _ => 1)
    (fun P _ => P.prime) (fun P _ P' _ h h' => h (HeightOneSpectrum.ext h')) x
  have key : ∀ P : S, Ideal.Quotient.mk P.1.asIdeal y = (c P : kP P.1) := fun P => by
    rw [← hx P]
    exact Ideal.Quotient.eq.2 (by simpa using hy P.1 P.2)
  refine ⟨y, ?_, key⟩
  rintro rfl
  have := Q.isPrime
  exact (c ⟨Q, hQ⟩).ne_zero ((key ⟨Q, hQ⟩).symm.trans (map_zero _))

theorem res_of_mul_eq (P : Pl E) {p u w : Formalism.L2.Herm.intAf F E} (hp : resS F P p = 1) (h : p * u = p * w) :
    resS F P u = resS F P w := by
  have := congrArg (resS F P) h
  rwa [map_mul, map_mul, hp, one_mul, one_mul] at this

end Frame

section Adelic

open GlobalTheory.LevSplit

variable {D : D7}

theorem exists_idemSum (P : Finset (Pl D.host.E)) (h : ∀ Q ∈ P, ∀ Q' ∈ P, ¬ Lev.IsConjPl Q Q') :
    ∃ e : Formalism.L2.Theta.AE D, IsIdemSum e P :=
  GlobalTheory.GridIdem.exists_isIdemSum P (fun Q hQ => GlobalTheory.ParahoricLift.exists_isIdemAt (h Q hQ Q hQ))
    fun Q hQ Q' hQ' e => (GlobalTheory.IdemSupport.eq_or_eq_cP e).resolve_right fun e' =>
      h Q' hQ' Q hQ ((GlobalTheory.IdemSupport.isConjPl_iff Q' Q).2 e')

theorem sum_mul_mem {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (B : Subring R') (p : ι → R) (c : R)
    (s : Finset ι) (h : ∀ i ∈ s, f (p i * c) ∈ B) : f ((∑ i ∈ s, p i) * c) ∈ B := by
  rw [Finset.sum_mul, map_sum]; exact sum_mem h

theorem idemSum_div_int {e : Formalism.L2.Theta.AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {a : 𝓞 D.host.E}
    (h0 : a ≠ 0) (ha : ∀ P ∈ S, a ∉ P.asIdeal) :
    finSw D (e * incA D ((a : D.host.E)⁻¹)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  exact sum_mul_mem (finSw D) _ es _ S fun P hP =>
    swapAE_int (not_not.1 fun hn => ha P hP (((hes P hP).2 a h0).2 hn))

theorem unit_aux {R T : Type} [CommRing R] [CommRing T] (c : R →+* R) (hc : ∀ x, c (c x) = x) (f : R →+* T)
    (B : Subring T) (hB : ∀ x, f x ∈ B → f (c x) ∈ B) {e a ai : R} (h1 : e * e = e) (h2 : e * c e = 0) (ha : a * ai = 1)
    (i1 : f e ∈ B) (i2 : f a ∈ B) (i3 : f (e * ai) ∈ B) :
    ∃ u, u * c u = 1 ∧ f u ∈ B ∧ (e + c e) * (u - 1) = u - 1 ∧ e * u = e * a := by
  have h3 : c e * c e = c e := by rw [← map_mul, h1]
  have hb : c a * c ai = 1 := by rw [← map_mul, ha, map_one]
  refine ⟨e * a + c e * c ai + (1 - e - c e), ?_, ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, map_sub, map_one, hc]
    rw [sub_right_comm 1 (c e) e]
    exact glued_idempotent_units_mul_eq_one h1 h2 h3 ha hb
  · rw [← map_mul c, map_add, map_add, map_sub, map_sub, map_one, map_mul]
    exact add_mem (add_mem (mul_mem i1 i2) (hB _ i3)) (sub_mem (sub_mem (one_mem _) i1) (hB _ i1))
  · linear_combination (a - 1) * h1 + (a + c ai - 2) * h2 + (c ai - 1) * h3
  · linear_combination (a - 1) * h1 + (c ai - 1) * h2

theorem finSw_cA_int (x : Formalism.L2.Theta.AE D) (h : finSw D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    finSw D (cA D x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [finSw_cA]
  exact sigR_int h

theorem exists_norm_one {e : Formalism.L2.Theta.AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    (c : ∀ P : S, (kP P.1)ˣ) : ∃ u : Formalism.L2.Theta.AE D, u * cA D u = 1 ∧ (e + cA D e) * (u - 1) = u - 1 ∧
      ∃ hu : finSw D u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
        ∀ P : S, resS D.host.F P.1 ⟨finSw D u, hu⟩ = (c P : kP P.1) := by
  obtain ⟨a, h0, ha⟩ := exists_int_res S c
  have hn : ∀ P ∈ S, a ∉ P.asIdeal := fun P hP h => by
    have := P.isPrime
    exact (c ⟨P, hP⟩).ne_zero ((ha ⟨P, hP⟩).symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 h))
  have h0' : (a : D.host.E) ≠ 0 := fun h => h0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨i1, r1⟩ := GlobalTheory.TameProd.resS_idemSum he
  have i1' : finSw D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := i1
  have i2 : finSw D (incA D (a : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (oToS D.host.F D.host.E a).2
  have hai : incA D (a : D.host.E) * incA D ((a : D.host.E)⁻¹) = 1 := by
    rw [← RingHom.map_mul, mul_inv_cancel₀ h0', RingHom.map_one]
  obtain ⟨u, u1, u2, u3, u4⟩ := unit_aux (cA D) Formalism.L2.Theta.cA_cA (finSw D) _ finSw_cA_int
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hai i1' i2 (idemSum_div_int he h0 hn)
  refine ⟨u, u1, u3, u2, fun P => ?_⟩
  have e1 : (⟨finSw D e, i1'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨finSw D u, u2⟩ =
      ⟨finSw D e, i1'⟩ * oToS D.host.F D.host.E a :=
    Subtype.ext (((finSw D).map_mul _ _).symm.trans ((congrArg (finSw D) u4).trans ((finSw D).map_mul _ _)))
  exact (res_of_mul_eq P.1 (r1 P.1 P.2) e1).trans ((resS_oToS P.1 a).trans (ha P))

theorem exists_central_lift (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {e : Formalism.L2.Theta.AE D} (he : IsIdemSum e L.Pg) {g : G0 L.Pg L.r} (hg : ∀ x, x * g = g * x) :
    ∃ ζ ∈ Subgroup.center (GA D V), SuppAt e V ζ ∧ Lev.IsLevelLift V β L g ζ := by
  choose c hc using scalar_of_center hg
  obtain ⟨u, u1, u2, hu, u3⟩ := exists_norm_one he c
  obtain ⟨ζ, hζ⟩ : ∃ ζ : GA D V, mt V ζ = u • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) :=
    ⟨⟨scal V.rank u1, scal_mem _ _ u1⟩, rfl⟩
  have hs : SuppAt e V ζ := fun i j => by
    rw [hζ]
    exact smul_one_supp u2 i j
  have h0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hf : ζ ∈ GfC V := GlobalTheory.IdemSupport.mem_GfC_of_suppF V (f := e + cA D e)
    (by rw [RingHom.map_add, h0, GlobalTheory.PlaceDatum.infPart_cA h0, add_zero]) hs
  have huv : (⟨finSw D u, hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨finSw D (cA D u), finSw_cA_int u hu⟩ = 1 :=
    Subtype.ext (((finSw D).map_mul _ _).symm.trans ((congrArg (finSw D) u1).trans (finSw D).map_one))
  have hx : (Lev.finE V ζ).1 = finSw D u • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) := by
    rw [finE_val, hζ]
    exact map_smul_one _ _
  obtain ⟨hS, hr⟩ := scalar_mem_St β huv hx
  refine ⟨ζ, Subgroup.mem_center_iff.2 fun y => GlobalTheory.IdemSupport.mt_inj V ?_, hs, hf,
    mem_parLev.2 ⟨finE_mem_UA V _, hS, fun P _ => blockTri_of_scalar _ (hr P), fun P _ => blockTri_of_scalar _ (hr P)⟩,
    funext fun P => blockRestriction_of_scalar_eq_scalar L.hr (hr P.1) ?_⟩
  · rw [GlobalTheory.IdemSupport.mt_mul, GlobalTheory.IdemSupport.mt_mul, hζ]
    exact smul_one_comm _ _
  · rw [u3 P]
    exact hc P

end Adelic

theorem inner_eq_of_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →ₗ[ℂ] H)
    (h : ∀ x, ‖T x‖ = ‖x‖) (y y' : H) : ⟪T y, T y'⟫_ℂ = ⟪y, y'⟫_ℂ :=
  LinearIsometry.inner_map_map ⟨T, h⟩ y y'

theorem comm_of_center {G H : Type*} [Group G] [AddCommGroup H] [Module ℂ H] (ρ : Representation ℂ G H) {z : G}
    (hz : z ∈ Subgroup.center G) (g : G) (y : H) : ρ z (ρ g y) = ρ g (ρ z y) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.mem_center_iff.1 hz g, map_mul, Module.End.mul_apply]

theorem map_center {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {z : G} (hz : z ∈ Subgroup.center G) (x : H) :
    x * φ z = φ z * x := by
  obtain ⟨g, rfl⟩ := φ.surjective x
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]

theorem exists_isCentralShift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), ∀ z ∈ Subgroup.center G, ∃ ζ, IsCentralShift R i σ z ζ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ z hz
  obtain ⟨e, he⟩ := exists_idemSum R.Pg (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg)
  have h := exists_central_lift (Wc D i) (R.βW i) (R.datWp i R.triv) he (g := R.eG z) (map_center R.eG hz)
  obtain ⟨ζ, hc, hs, hl⟩ := h
  have ht : ∀ y v h, (R.HW i σ).e (R.gW i σ z y) v h = (R.HW i σ).e y v (h * ζ) := fun y v h =>
    (congrArg (fun T : MMap (R.MW i σ) => T v h) (hC.models.gW i σ z y)).trans
      (GlobalTheory.GeoActCompare.actW_apply R hC.models.HW σ hl y v h)
  refine ⟨ζ, hz, hc, hl.1, ⟨e, he, hs⟩, hl, ht,
    inner_eq_of_norm (R.gW i σ z) (GlobalTheory.gW_norm_eq R hC.models.HW hC.models.gW hC.models.νW i σ z),
    comm_of_center (R.gW i σ) hz, fun _ _ S _ y y' h => ?_⟩
  refine MultilinearMap.ext fun v => funext fun g => (ht y' v g).trans ?_
  refine (congrArg (fun T : MMap (R.MW i σ) => T v (g * ζ)) h).trans ?_
  show ∑ γ ∈ S, (R.HW i σ).e y v (g * ζ * γ) = ∑ γ ∈ S, (R.HW i σ).e (R.gW i σ z y) v (g * γ)
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [ht, mul_assoc, mul_assoc, Subgroup.mem_center_iff.1 hc γ]

end GlobalTheory.CentralShift

end
