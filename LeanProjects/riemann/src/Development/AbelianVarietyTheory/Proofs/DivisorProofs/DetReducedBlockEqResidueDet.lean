import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
open scoped TensorProduct

namespace GlobalTheory.GeoLevel

theorem finite_root_near (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) (n : ℕ)
    (u w w' z : RA F E) (huO : u ∈ intHat F E) (hwO : w ∈ intHat F E) (hwO' : w' ∈ intHat F E) (hz : z ∈ intHat F E)
    (hu : u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1) (hw : w = u * sg (FiniteAdeleRing (𝓞 F) F) c w)
    (hww : w * w' = 1 + n * z) :
    ∃ x y : RA F E, x ∈ intHat F E ∧ y ∈ intHat F E ∧ x * y = 1 ∧
      x = u * sg (FiniteAdeleRing (𝓞 F) F) c x ∧ ∃ p ∈ intHat F E, x = w + n * p := by
  obtain ⟨x₁, hx₁, ⟨y₁, hy₁, hxy₁⟩, hr₁⟩ := GlobalTheory.T.exists_integral_unit_root_norm_one_adele F E c h2 hc hP u huO hu
  obtain ⟨e, f, hee, hef, hun⟩ :=
    exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) n
  obtain ⟨y₀, hy₀⟩ := (unit_of_integral (inclHat F E) (inclHat_integral F E) (e * n) hun ⟨z, hz⟩).exists_right_inv
  have hse : sg (FiniteAdeleRing (𝓞 F) F) c (inclHat F E e : RA F E) = (inclHat F E e : RA F E) := by
    change sg (FiniteAdeleRing (𝓞 F) F) c (incl F e ⊗ₜ[F] (1 : E)) = incl F e ⊗ₜ[F] (1 : E)
    simp [sg]
  have hee' : (inclHat F E e : RA F E) * inclHat F E e = inclHat F E e := by
    rw [← Subring.coe_mul, ← map_mul, hee]
  have hef' : 1 - (inclHat F E e : RA F E) = n * inclHat F E f := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hef
    simpa using this
  have hy₀' : (1 + (inclHat F E e : RA F E) * n * z) * y₀ = 1 := by
    have := congrArg (fun t : intHat F E => (t : RA F E)) hy₀
    simpa using this
  have heO := (inclHat F E e).2
  have hfO := (inclHat F E f).2
  have hy₀O := y₀.2
  generalize (inclHat F E e : RA F E) = e' at *
  generalize (inclHat F E f : RA F E) = f' at *
  generalize (y₀ : RA F E) = y' at *
  have hx₁' : x₁ ∈ intHat F E := hx₁
  have hy₁' : y₁ ∈ intHat F E := hy₁
  have he1 := sub_mem (one_mem (intHat F E)) heO
  refine ⟨e' * w + (1 - e') * x₁, e' * (w' * y') + (1 - e') * y₁, add_mem (mul_mem heO hwO) (mul_mem he1 hx₁'),
    add_mem (mul_mem heO (mul_mem hwO' hy₀O)) (mul_mem he1 hy₁'), ?_, ?_, f' * (x₁ - w),
    mul_mem hfO (sub_mem hx₁' hwO), ?_⟩
  · linear_combination e' * hy₀' + (1 - e') * hxy₁ + e' * y' * hww +
      (w * w' * y' - w * y₁ - x₁ * w' * y' + x₁ * y₁ - n * z * y') * hee'
  · rw [map_add, map_mul _ (1 - e'), map_mul _ e', map_sub, map_one, hse]
    linear_combination e' * hw + (1 - e') * hr₁
  · linear_combination (x₁ - w) * hef'

end GlobalTheory.GeoLevel
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links
  Formalism.L2.JoinChr Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR.Lev
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

variable {D : D7}

noncomputable def unswap (D : D7) : EAf D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm.toAlgHom.toRingHom

theorem unswap_swap (z : Af D.host.F ⊗[D.host.F] D.host.E) : unswap D (swapAE D z) = z :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply z

theorem swap_unswap (z : EAf D) : swapAE D (unswap D z) = z :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).apply_symm_apply z

theorem unswap_int (z : Formalism.L2.Herm.intAf D.host.F D.host.E) : unswap D z ∈ intAE D := by
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact GlobalTheory.PlaceDatum.comm_symm_mem z.2

theorem valued_coe_int (P : Pl D.host.E) (a : 𝓞 D.host.E) :
    Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (a : D.host.E)) = P.intValuation a := by
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := D.host.E)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _

theorem valued_sub_le (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x)
    (h2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) (P : Pl D.host.E)
    (X : Formalism.L2.Herm.intAf D.host.F D.host.E) (a : 𝓞 D.host.E) (h : resS D.host.F P X = Ideal.Quotient.mk _ a) :
    Valued.v (ι (unswap D X) P - algebraMap D.host.E _ (a : D.host.E)) ≤ WithZero.exp (-1 : ℤ) := by
  let ev : FiniteAdeleRing (𝓞 D.host.E) D.host.E →+* P.adicCompletion D.host.E :=
    RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.adicCompletion D.host.E) P
  let φ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* P.adicCompletion D.host.E :=
    ev.comp ((ι : _ →+* _).comp ((unswap D).comp (Subring.subtype _)))
  have hφ : ∀ b : 𝓞 D.host.E, φ (oToS D.host.F D.host.E b) = algebraMap D.host.E _ (b : D.host.E) := fun b =>
    congrArg ev (h1 (b : D.host.E))
  have key : ∀ z ∈ idS D.host.F P.asIdeal, Valued.v (φ z) ≤ WithZero.exp (-1 : ℤ) := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ => Valued.v (φ z) ≤ WithZero.exp (-1 : ℤ)) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨b, hb, rfl⟩
      rw [hφ, valued_coe_int]
      have := (P.intValuation_le_pow_iff_mem b 1).2 (by simpa using hb)
      simpa using this
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact Valuation.map_add_le _ hx hy
    · intro c x _ hx
      rw [smul_eq_mul, map_mul, map_mul]
      calc _ ≤ 1 * WithZero.exp (-1 : ℤ) := mul_le_mul' ((h2 _).1 (unswap_int c) P) hx
        _ = _ := one_mul _
  have hm : X - oToS D.host.F D.host.E a ∈ idS D.host.F P.asIdeal := by
    rw [← Ideal.Quotient.eq]
    exact (RingEquiv.ofBijective (cmpS D.host.F P.asIdeal) (cmpS_bij P.asIdeal P.ne_bot)).symm.injective
      (h.trans (resS_oToS P a).symm)
  have := key _ hm
  rwa [map_sub, hφ] at this

theorem loc_eq_of_tame {χ : HChar D.host.E} {P : Pl D.host.E} (ht : χ.TameAt P) {s t : (P.adicCompletion D.host.E)ˣ}
    (hs : IsUnitAt P s) (h : Valued.v ((s : P.adicCompletion D.host.E) - t) ≤ WithZero.exp (-1 : ℤ)) :
    χ.loc P t = χ.loc P s := by
  have hs' : Valued.v ((s⁻¹ : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hs, inv_one]
  have e : ((t * s⁻¹ : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1 =
      -(((s : P.adicCompletion D.host.E) - t) * (s⁻¹ : (P.adicCompletion D.host.E)ˣ)) := by
    rw [sub_mul, Units.mul_inv, Units.val_mul]; ring
  have h1 : Valued.v (((t * s⁻¹ : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1) ≤ WithZero.exp (-1 : ℤ) := by
    rw [e, Valuation.map_neg, map_mul, hs', mul_one]; exact h
  have h2 : IsUnitAt P (t * s⁻¹) := by
    have h3 := Valuation.map_one_add_of_lt Valued.v (h1.trans_lt (by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)))
    rwa [add_sub_cancel] at h3
  have := ht _ h2 h1
  rwa [map_mul, map_inv, mul_inv_eq_one] at this

theorem char_finUnit {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (hc : ChrEq c χ) (ht : ∀ P, χ.TameAt P)
    (Pg : Finset (Pl D.host.E)) (ch : ∀ P : Pl D.host.E, (kP P)ˣ →* ℂˣ) (hres : ∀ P ∈ Pg, IsRes χ P (ch P))
    {x : (AE D)ˣ} (hx : FinUnit x) (X : Formalism.L2.Herm.intAf D.host.F D.host.E) (hX : unswap D X = finPart D (x : AE D))
    (u : ∀ P : Pg, (kP P.1)ˣ) (hu : ∀ P : Pg, (u P : kP P.1) = resS D.host.F P.1 X)
    (hoff : ∀ P ∉ Pg, χ.UnrAt P ∨ resS D.host.F P X = 1) :
    ((c x : Circle) : ℂ) = ∏ P : Pg, ((ch P.1 (u P) : ℂˣ) : ℂ) := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  have hM : 0 < ∏ P ∈ Pg, Ideal.absNorm P.asIdeal :=
    Finset.prod_pos fun P _ => Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E _ (Nat.mul_pos hN hM)
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have hsub : Pg ⊆ S := fun P hP => by
    by_contra h
    refine (hS' P h).2 ?_
    rw [Nat.cast_mul, ← Finset.mul_prod_erase _ _ hP, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))
  have key := hprod x hx1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1.trans (by
      refine mul_le_mul_left ?_ _
      rw [Nat.cast_mul, map_mul]
      refine mul_le_of_le_one_right' ?_
      rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E)]
      exact P.valuation_le_one _)⟩)
    (fun P hP => ⟨(hS' P hP).1, fun h => (hS' P hP).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)⟩)
  have loc : ∀ P ∈ S, IsUnitAt P (atFin P (k P)) ∧ ∀ (a : 𝓞 D.host.E) (k' : D.host.Eˣ), (k' : D.host.E) = a →
      resS D.host.F P X = Ideal.Quotient.mk _ a → χ.locK P k' = χ.locK P (k P) := fun P hP => by
    obtain ⟨a, -, b⟩ := hS P hP
    have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := a
    have b' : Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
        WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k P : D.host.E) := b
    rw [hv P] at a'
    rw [← a', mul_one] at b'
    have hun : IsUnitAt P (atFin P (k P)) := by
      show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
    refine ⟨hun, fun a k' hk' ha => loc_eq_of_tame (ht P) hun ?_⟩
    have h4 := valued_sub_le ι h1 h2 P X a ha
    rw [hX, ← hk'] at h4
    have h5 := Valuation.map_sub_le _ h4 b'
    rwa [sub_sub_sub_cancel_left] at h5
  rw [key, ← Finset.prod_subset hsub, ← Finset.prod_coe_sort Pg]
  · refine Finset.prod_congr rfl fun P _ => congrArg _ ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u P : kP P.1)
    have h0 : (a : D.host.E) ≠ 0 := fun h => by
      have : a = 0 := RingOfIntegers.coe_injective h
      exact (u P).ne_zero (by rw [← ha, this, map_zero])
    rw [hres P.1 P.2 a (Units.mk0 _ h0) (u P) rfl ha.symm]
    exact ((loc P.1 (hsub P.2)).2 a _ rfl ((hu P).symm.trans ha.symm)).symm
  · intro P hP hP'
    rcases hoff P hP' with h | h
    · exact congrArg Units.val (h _ (loc P hP).1)
    · rw [← (loc P hP).2 1 1 rfl h, map_one, Units.val_one]

theorem swap_int {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    swapAE D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, rfl⟩ := hz
    exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [RingHom.map_add]; exact add_mem ha hb
  | neg a _ ha => rw [RingHom.map_neg]; exact neg_mem ha

theorem det_frGL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (frGL β y).1.det = ((y.1.det : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := by
  have h1 : Matrix.GeneralLinearGroup.det (β * intGL F E n y * β⁻¹) = Matrix.GeneralLinearGroup.det (intGL F E n y) := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  exact (congrArg Units.val h1).trans ((Formalism.L2.Herm.intAf F E).subtype.map_det _).symm

theorem det_reduced_block_eq_residue_det {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r : ℕ} (hr : r ≤ n)
    (he : r = n) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (P : Pl E)
    (h : redFn β P (frGL β y) ∈ blockTri (blk2 r)) :
    ((Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn β P (frGL β y))) : (kP P)ˣ) : kP P) = resS F P y.1.det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, upper_block_val_submatrix _ h, redFn_frGL, RingHom.map_det]
  exact Matrix.det_submatrix_equiv_self (finCongr he) _

theorem root_sum {R : Type} [CommRing R] (σ : R →+* R) {a b u : R} (ha : σ a = b) (hb : σ b = a) (hu : u * σ u = 1) :
    a + b * u = u * σ (a + b * u) := by
  rw [map_add, map_mul, ha, hb]
  linear_combination (-a) * hu

theorem root_sum_mul {R : Type} [CommRing R] {a b u u' m s s' : R} (hu : u * u' = 1) (e1 : a + b = 1 + m * s)
    (e2 : a * b = m * s') : (a + b * u) * (a + b * u') = 1 + m * (s * (a + b + 1) + s' * (u + u' - 2)) := by
  linear_combination (a + b + 1) * e1 + (u + u' - 2) * e2 + b ^ 2 * hu

theorem exists_det_of_lift {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : L.r = V.rank)
    {g₀ : G0 L.Pg L.r} {k : GA D V} (hk : IsLevelLift V β L g₀ k) :
    ∃ U : Formalism.L2.Herm.intAf D.host.F D.host.E, unswap D U = (finHom V k).1.det ∧
      ∀ P : L.Pg, ((Matrix.GeneralLinearGroup.det (g₀ P) : (kP P.1)ˣ) : kP P.1) = resS D.host.F P.1 U := by
  obtain ⟨y, hy⟩ := parLev_St hk.2.1
  refine ⟨y.1.det, ?_, fun P => ?_⟩
  · have h2 : swapAE D (finHom V k).1.det = (finE V k).1.det := (swapAE D).map_det _
    rw [← det_frGL β y, hy, ← h2, unswap_swap]
  · have h1 := blockTri_blkOf_le _ _ (parLev_g hk.2.1 P.2)
    have h2 : g₀ P = upperLeftBlock L.hr (redFn β P.1 (finE V k)) := (congrFun hk.2.2 P).symm
    rw [← hy] at h1 h2
    rw [h2]
    exact det_reduced_block_eq_residue_det L.hr hr β y P.1 h1

theorem isDetRoot_of_fin {V : HSp D} {k : GA D V} (hk : k ∈ GfC V) {x : (AE D)ˣ} (h1 : infPart D (x : AE D) = 1)
    (h2 : finPart D (x : AE D) = (finHom V k).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D))) :
    IsDetRoot V k x := by
  have e1 : infPart D (matHom V k).1.det = 1 := by
    have h : infHom V k = 1 := hk
    have h' : (infHom V k).1.det = 1 := by rw [h]; exact Matrix.det_one
    exact ((infPart D).map_det _).trans h'
  have e2 : finPart D (matHom V k).1.det = (finHom V k).1.det := (finPart D).map_det _
  refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
  · rw [RingHom.map_mul, e1, one_mul]
    exact h1.trans ((GlobalTheory.PlaceIdem.infPart_cA D _).trans (by rw [h1, RingHom.map_one])).symm
  · rw [RingHom.map_mul, e2]
    exact h2.trans (congrArg _ (GlobalTheory.PlaceIdem.finPart_cA D _).symm)

set_option maxHeartbeats 400000 in

theorem exists_root_half (m : ℕ) (U : Formalism.L2.Herm.intAf D.host.F D.host.E) (a b s s' : 𝓞 D.host.E)
    (hb : (b : D.host.E) = star (a : D.host.E)) (hs : a + b = 1 + m * s) (hs' : a * b = m * s')
    (hn : unswap D U * sigR (Af D.host.F) D.sp.cm.sig (unswap D U) = 1) :
    ∃ y y', y ∈ intAE D ∧ y' ∈ intAE D ∧ y * y' = 1 ∧ y = unswap D U * sigR (Af D.host.F) D.sp.cm.sig y ∧
      ∃ p ∈ intAE D, y = unswap D (oToS D.host.F D.host.E a) + unswap D (oToS D.host.F D.host.E b) * unswap D U + m * p := by
  have hP : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal →
      ∃ t s : 𝓞 D.host.E, (s : D.host.E) = GlobalTheory.Member.cF D (t : D.host.E) ∧ t - s ∉ P := fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    exact ⟨θ, t, ht, hθ⟩
  have hc1 : GlobalTheory.Member.cF D ≠ 1 := by
    intro h
    obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    obtain ⟨t, s, hs, hts⟩ := hP P hM
    rw [h] at hs
    have : s = t := Subtype.ext hs
    rw [this, sub_self] at hts
    exact hts P.zero_mem
  let j : 𝓞 D.host.E →+* Af D.host.F ⊗[D.host.F] D.host.E :=
    (unswap D).comp ((Subring.subtype _).comp (oToS D.host.F D.host.E))
  let σ := sigR (Af D.host.F) D.sp.cm.sig
  have hO : ∀ z, z ∈ GlobalTheory.AdLat.RootNear.intHat D.host.F D.host.E ↔ z ∈ intAE D := fun z => by
    rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; rfl
  have hj : ∀ t, j t ∈ GlobalTheory.AdLat.RootNear.intHat D.host.F D.host.E := fun t => (hO _).2 (unswap_int (oToS D.host.F D.host.E t))
  have hσa : σ (j a) = j b := by
    show (1 : Af D.host.F) ⊗ₜ[D.host.F] star (a : D.host.E) = 1 ⊗ₜ[D.host.F] (b : D.host.E)
    rw [hb]
  have hσb : σ (j b) = j a := by
    show (1 : Af D.host.F) ⊗ₜ[D.host.F] star (b : D.host.E) = 1 ⊗ₜ[D.host.F] (a : D.host.E)
    rw [hb, star_star]
  have hu := (hO _).2 (unswap_int U)
  have hu' := (hO _).2 (GlobalTheory.PlaceIdem.sig_mem D (unswap_int U))
  have e1 : j a + j b = 1 + m * j s := by rw [← map_add, hs, map_add, map_one, map_mul, map_natCast]
  have e2 : j a * j b = m * j s' := by rw [← map_mul, hs', map_mul, map_natCast]
  have key := finite_root_near D.host.F D.host.E (GlobalTheory.Member.cF D) D.sp.cm.deg2 hc1 hP m
    (unswap D U) (j a + j b * unswap D U) (j a + j b * σ (unswap D U))
    (j s * (j a + j b + 1) + j s' * (unswap D U + σ (unswap D U) - 2)) hu
    (add_mem (hj a) (mul_mem (hj b) hu)) (add_mem (hj a) (mul_mem (hj b) hu'))
    (add_mem (mul_mem (hj s) (add_mem (add_mem (hj a) (hj b)) (one_mem _)))
      (mul_mem (hj s') (sub_mem (add_mem hu hu') (ofNat_mem _ 2)))) hn
    (root_sum σ hσa hσb hn) (root_sum_mul hn e1 e2)
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact key

theorem resS_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : Pl E) {a b s m : 𝓞 E}
    (U p : Formalism.L2.Herm.intAf F E) (hs : a + b = 1 + m * s) (hm : m ∈ P.asIdeal) :
    resS F P (oToS F E a + oToS F E b * U + oToS F E m * p) = Ideal.Quotient.mk _ a + Ideal.Quotient.mk _ b * resS F P U ∧
      Ideal.Quotient.mk P.asIdeal a + Ideal.Quotient.mk _ b = 1 := by
  have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
  constructor
  · rw [map_add, map_add, map_mul, map_mul, resS_oToS, resS_oToS, resS_oToS, h0, zero_mul, add_zero]
  · rw [← map_add, hs, map_add, map_mul, h0, zero_mul, add_zero, map_one]

theorem resS_sum_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : Pl E) {a b s m : 𝓞 E}
    (U p : Formalism.L2.Herm.intAf F E) (hs : a + b = 1 + m * s) (hm : m ∈ P.asIdeal) (ha : a ∈ P.asIdeal) :
    resS F P (oToS F E a + oToS F E b * U + oToS F E m * p) = resS F P U := by
  obtain ⟨h1, h2⟩ := resS_sum P U p hs hm
  have h0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
  rw [h0, zero_add] at h2
  rw [h1, h0, h2, zero_add, one_mul]

theorem resS_sum_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : Pl E) {a b s m : 𝓞 E}
    (U p : Formalism.L2.Herm.intAf F E) (hs : a + b = 1 + m * s) (hm : m ∈ P.asIdeal) (hb : b ∈ P.asIdeal) :
    resS F P (oToS F E a + oToS F E b * U + oToS F E m * p) = 1 := by
  obtain ⟨h1, h2⟩ := resS_sum P U p hs hm
  have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hb
  rw [h0, add_zero] at h2
  rw [h1, h0, h2, zero_mul, add_zero]

theorem map_coe_sum {R B : Type} [CommRing R] [CommRing B] (S : Subring R) (f : R →+* B) (a b u m' p : S) (m : ℕ) (hm : m' = m) :
    f ((a + b * u + m' * p : S) : R) = f a + f b * f u + m * f p := by
  subst hm
  simp

set_option maxHeartbeats 400000 in

theorem exists_root_char {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : L.r = V.rank)
    {g₀ : G0 L.Pg L.r} {k : GA D V} (hk : IsLevelLift V β L g₀ k) {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (hc : ChrEq c χ)
    (ht : ∀ P, χ.TameAt P) (m : ℕ) (hun : ∀ P : Pl D.host.E, (m : 𝓞 D.host.E) ∉ P.asIdeal → χ.UnrAt P)
    (ch : ∀ P : Pl D.host.E, (kP P)ˣ →* ℂˣ) (hres : ∀ P ∈ L.Pg, IsRes χ P (ch P)) (a b s s' : 𝓞 D.host.E)
    (hb : (b : D.host.E) = star (a : D.host.E)) (hs : a + b = 1 + m * s) (hs' : a * b = m * s')
    (hin : ∀ P ∈ L.Pg, a ∈ P.asIdeal ∧ (m : 𝓞 D.host.E) ∈ P.asIdeal)
    (hout : ∀ P ∉ L.Pg, (m : 𝓞 D.host.E) ∈ P.asIdeal → b ∈ P.asIdeal) :
    ∃ x, FinUnit x ∧ IsDetRoot V k x ∧
      ((c x : Circle) : ℂ) = ∏ P : L.Pg, ((ch P.1 (Matrix.GeneralLinearGroup.det (g₀ P)) : ℂˣ) : ℂ) := by
  obtain ⟨U, hU, hUP⟩ := exists_det_of_lift hr hk
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hyp⟩ := exists_root_half m U a b s s' hb hs hs'
    (by rw [hU]; exact GlobalTheory.RecDict.det_finHom_norm V k)
  obtain ⟨x, hx1, hx2, hx3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  have hx : FinUnit x := ⟨hx1, hx2 ▸ hy, hx3 ▸ hy'⟩
  refine ⟨x, hx, isDetRoot_of_fin hk.1 hx1 (by rw [hx2, ← hU]; exact hroot), ?_⟩
  let p' : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨swapAE D p, swap_int hp⟩
  refine char_finUnit hc ht L.Pg ch hres hx (oToS _ _ a + oToS _ _ b * U + oToS _ _ m * p') ?_ _ (fun P => ?_) fun P hP => ?_
  · rw [hx2, hyp, ← unswap_swap p]
    exact map_coe_sum _ (unswap D) _ _ U _ p' m (map_natCast _ m)
  · exact (hUP P).trans (resS_sum_left P.1 U p' hs (hin P.1 P.2).2 (hin P.1 P.2).1).symm
  · by_cases hm : (m : 𝓞 D.host.E) ∈ P.asIdeal
    · exact Or.inr (resS_sum_right P U p' hs hm (hout P hP hm))
    · exact Or.inl (hun P hm)

theorem exists_half_elements {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Pg : Finset (Pl E)) (h : ∀ P : Pl E, P ∈ Pg ↔ l.Mb ≤ P.asIdeal) :
    ∃ a b s s' : 𝓞 E, (b : E) = IsCMField.complexConj E (a : E) ∧ a + b = 1 + l.M * s ∧ a * b = l.M * s' ∧
      (∀ P ∈ Pg, a ∈ P.asIdeal ∧ (l.M : 𝓞 E) ∈ P.asIdeal) ∧
      ∀ P ∉ Pg, (l.M : 𝓞 E) ∈ P.asIdeal → b ∈ P.asIdeal := by
  have hbar := H.bar_eq
  have hbb : ∀ t : 𝓞 E, H.bar (H.bar t) = t := fun t =>
    RingOfIntegers.ext (by rw [hbar, hbar, IsCMField.complexConj_apply_apply])
  obtain ⟨a, ha, a', ha', haa⟩ := Submodule.mem_sup.1 (l.coprime.ge (Submodule.mem_top (x := (1 : 𝓞 E))))
  have hb : H.bar a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ ha
  have hb' : H.bar a' ∈ l.Mb := by
    obtain ⟨t, ht, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 ha'
    exact (hbb t).symm ▸ ht
  have hbb' : H.bar a + H.bar a' = 1 := by rw [← map_add, haa, map_one]
  have h1 : a + H.bar a - 1 ∈ Ideal.span {(l.M : 𝓞 E)} := by
    rw [← l.prod, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 l.coprime)]
    refine ⟨?_, ?_⟩
    · have : a + H.bar a - 1 = a - H.bar a' := by linear_combination hbb'
      exact this ▸ sub_mem ha hb'
    · have : a + H.bar a - 1 = H.bar a - a' := by linear_combination haa
      exact this ▸ sub_mem hb ha'
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h1
  obtain ⟨s', hs'⟩ := Ideal.mem_span_singleton'.1 (l.prod.le (Ideal.mul_mem_mul ha hb))
  refine ⟨a, H.bar a, s, s', hbar a, by linear_combination -hs, by linear_combination -hs', fun P hP => ?_, fun P hP hm => ?_⟩
  · have hle : l.Mb ≤ P.asIdeal := (h P).1 hP
    exact ⟨hle ha, hle (Ideal.mul_le_left (l.prod.ge (Ideal.mem_span_singleton_self _)))⟩
  · rcases P.isPrime.mul_le.1 (l.prod.le.trans ((Ideal.span_singleton_le_iff_mem _).2 hm)) with h2 | h2
    · exact absurd ((h P).2 h2) hP
    · exact h2 hb

end GlobalTheory.GeoLevel
