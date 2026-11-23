import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormNonvanishing

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalCentral

noncomputable def scalGL (n : ℕ) {S : Type} [CommRing S] {m : ℤ} (h : IsUnit (m : S)) : GL (Fin n) S :=
  Units.map (Matrix.scalar (Fin n)).toMonoidHom h.unit

theorem scalGL_val (n : ℕ) {S : Type} [CommRing S] {m : ℤ} (h : IsUnit (m : S)) :
    (scalGL n h).1 = m • (1 : Matrix (Fin n) (Fin n) S) := by
  show Matrix.scalar (Fin n) (m : S) = _
  rw [Matrix.scalar_apply, ← Int.cast_smul_eq_zsmul S m (1 : Matrix (Fin n) (Fin n) S), Matrix.smul_one_eq_diagonal]

theorem scalGL_comm {n : ℕ} {S : Type} [CommRing S] {m : ℤ} (h : IsUnit (m : S)) (x : GL (Fin n) S) :
    x * scalGL n h = scalGL n h * x :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, scalGL_val, mul_smul_comm, smul_mul_assoc, mul_one, one_mul])

theorem isUnit_of_coprime {S : Type} [CommRing S] {m M : ℤ} (h : IsCoprime m M) (h0 : (M : S) = 0) : IsUnit (m : S) := by
  obtain ⟨a, b, e⟩ := h
  have e' : (m : S) * (a : S) = 1 := by
    have := congrArg (Int.cast : ℤ → S) e
    push_cast at this
    rw [h0, mul_zero, add_zero, mul_comm] at this
    exact this
  exact ⟨⟨m, a, e', by rw [mul_comm]; exact e'⟩, rfl⟩

theorem map_int_one {n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (m : ℤ) (i j : Fin n) :
    f ((m • (1 : Matrix (Fin n) (Fin n) S)) i j) = (m • (1 : Matrix (Fin n) (Fin n) S')) i j := by
  rw [Matrix.smul_apply, Matrix.smul_apply, map_zsmul, Matrix.one_apply, Matrix.one_apply, apply_ite f, map_one, map_zero]

theorem cast_quot {O : Type} [CommRing O] (I : Ideal O) {M : ℕ} (h : (M : O) ∈ I) : (((M : ℕ) : ℤ) : O ⧸ I) = 0 := by
  rw [Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk I)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 h

theorem mem_of_prod {O : Type} [CommRing O] (A : Ideal O) {I J : Ideal O} {x : O} (hA : A ≤ I) (h : A * J = Ideal.span {x})
    : x ∈ I := by
  have h0 : x ∈ A * J := by rw [h]; exact Ideal.mem_span_singleton_self x
  exact hA (Ideal.mul_le_inf h0).1

theorem cast_res {E : Type} [Field E] [NumberField E] (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)}) {P : Pl E} (hP : P ∈ T) : (((M : ℕ) : ℤ) : kP P) = 0 :=
  cast_quot P.asIdeal (mem_of_prod _ ((GlobalTheory.OneMapRef.Lift.mem_iff_prod_le T P).1 hP) hJ)

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem exists_matrix_int (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)}) {y : GL (Fin n) (Formalism.L2.Herm.intAf F E)} {m : ℤ}
    (h : ∀ P ∈ T, (Formalism.UG.bc (resS F P) y).1 = m • (1 : Matrix (Fin n) (Fin n) (kP P))) {b : 𝓞 E} (hb : b ∈ J) :
    ∃ s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E),
      oToS F E b • (y.1 - m • (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))) = M • s := by
  have key : ∀ i j, ∃ c, oToS F E b * (y.1 i j - (m • (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))) i j) = M • c := by
    intro i j
    have h1 : y.1 i j - (m • (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))) i j ∈ (∏ P ∈ T, P.asIdeal).map (oToS F E) :=
      GlobalTheory.LevelUnique.mem_map_prod _ T fun P hP => GlobalTheory.LevelUnique.sub_mem_idS
        ((congrArg (fun g : Matrix (Fin n) (Fin n) (kP P) => g i j) (h P hP)).trans (map_int_one (resS F P) m i j).symm)
    have h2 := Ideal.mul_mem_mul h1 (Ideal.mem_map_of_mem (oToS F E) hb)
    rw [← Ideal.map_mul, hJ, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton'] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [mul_comm, ← hc, nsmul_eq_mul, mul_comm]⟩
  choose c hc using key
  exact ⟨Matrix.of c, Matrix.ext fun i j => hc i j⟩

end Res

theorem conj_smul_sub_int {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) {y : GL (Fin n) S}
    {s : Matrix (Fin n) (Fin n) S} {b : S} {M : ℕ} {m : ℤ} (h : b • (y.1 - m • (1 : Matrix (Fin n) (Fin n) S)) = M • s) :
    (b : R) • ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 - m • (1 : Matrix (Fin n) (Fin n) R)) =
      M • (β.1 * s.map S.subtype * (β⁻¹).1) := by
  have e : (b : R) • ((Formalism.UG.bc S.subtype y).1 - m • (1 : Matrix (Fin n) (Fin n) R)) = M • s.map S.subtype := by
    ext i j
    have : S.subtype ((b • (y.1 - m • (1 : Matrix (Fin n) (Fin n) S))) i j) = S.subtype ((M • s) i j) := by rw [h]
    rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul, map_sub, map_int_one, map_nsmul] at this
    exact this
  have e2 : m • (1 : Matrix (Fin n) (Fin n) R) = β.1 * (m • (1 : Matrix (Fin n) (Fin n) R)) * (β⁻¹).1 := by
    rw [mul_smul_comm, mul_one, smul_mul_assoc, Units.mul_inv]
  rw [Units.val_mul, Units.val_mul, e2, ← sub_mul, ← mul_sub, ← smul_mul_assoc, ← mul_smul_comm, e, mul_smul_comm, smul_mul_assoc]

theorem exists_matrix_hat_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) (m : ℤ)
    (h : ∀ P ∈ T, (redFn β P x).1 = m • (1 : Matrix (Fin n) (Fin n) (kP P))) {b : 𝓞 E} (hb : b ∈ J)
    {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) •
          (K - m • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))) = M • N := by
  obtain ⟨y, rfl⟩ := hx
  simp only [redFn_frGL] at h
  obtain ⟨s, hs⟩ := exists_matrix_int T hJ h hb
  have e := conj_smul_sub_int _ β hs
  have hN := fun z hz => (hfr _).2 (GlobalTheory.LevelUnique.conj_mulVec_mem _ β s z ((hfr z).1 hz))
  generalize β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 = N at e hN
  refine ⟨N.map (Algebra.TensorProduct.comm F _ E).symm, fun z hz => ?_, Matrix.ext fun i j => ?_⟩
  · have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ (hN _ (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
    convert h4 using 1
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.symm_apply_apply, Matrix.map_apply]
  · apply (Algebra.TensorProduct.comm F _ E).injective
    rw [Matrix.smul_apply, Matrix.smul_apply, map_nsmul, Matrix.map_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, map_mul,
      Matrix.sub_apply, map_sub, ← hK]
    have e3 := map_int_one (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom m i j
    refine Eq.trans ?_ (congrFun (congrFun e i) j)
    exact congrArg (fun t => _ * (_ - t)) e3

variable {D : D7}

theorem exists_cong_int {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k : GA D V}
    (hk : Lev.finE V k ∈ St β) (m : ℤ)
    (h : ∀ P ∈ T, (redFn β P (Lev.finE V k)).1 = m • (1 : Matrix (Fin V.rank) (Fin V.rank) (kP P))) {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • ((finHom V k).1 *ᵥ z -
        (m • (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))) *ᵥ z) = M • w := by
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_matrix_hat_int hfr T hJ hk m h hb (K := (finHom V k).1) (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [← Matrix.sub_mulVec, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem eq_int_of_submatrix {n r : ℕ} (hr : n = r) (h : r ≤ n) {S : Type} [CommRing S] {x : Matrix (Fin n) (Fin n) S} {m : ℤ}
    (e : x.submatrix (Fin.castLE h) (Fin.castLE h) = m • (1 : Matrix (Fin r) (Fin r) S)) :
    x = m • (1 : Matrix (Fin n) (Fin n) S) := by
  subst hr
  exact e

theorem int_calc {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {x z w₂ w₃ : Fin n → R} {M : ℕ} {m : ℤ}
    (e₂ : x - K *ᵥ z = M • w₂) (e₃ : K *ᵥ z - (m • (1 : Matrix (Fin n) (Fin n) R)) *ᵥ z = M • w₃) :
    x - m • z = M • (w₂ + w₃) := by
  rw [smul_add, ← e₂, ← e₃, sub_add_sub_cancel, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem redFn_int {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : V.rank = L.r)
    {g : G0 L.Pg L.r} {k : GA D V} (hk : Lev.IsLevelLift V β L g k) (m : ℤ)
    (hg : ∀ P, (g P).1 = m • (1 : Matrix (Fin L.r) (Fin L.r) (kP P.1))) :
    ∀ P ∈ L.Pg, (redFn β P (Lev.finE V k)).1 = m • (1 : Matrix (Fin V.rank) (Fin V.rank) (kP P)) := by
  intro P hP
  have e : upperLeftBlock L.hr (redFn β P (Lev.finE V k)) = g ⟨P, hP⟩ := congrFun hk.2.2 ⟨P, hP⟩
  have e' := (congrArg Units.val e).trans (hg ⟨P, hP⟩)
  rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP))] at e'
  exact eq_int_of_submatrix hr L.hr e'

set_option maxHeartbeats 1000000 in

theorem central_lev : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ m : ℤ, IsCoprime m (T.Q.l.M : ℤ) → ∃ z ∈ Subgroup.center G, ∀ a ∈ Mfr T.Q.l • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La), ∃ b : (T.Q.Dw ((i : ℕ) + 1)).La, O.lev z a = m • a + T.Q.l.M • b := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hO m hm
  have hT := tie.laws
  have hL := hR.lev
  have hβ := hL.βW i
  have hι := GlobalTheory.LevelAction.latEmb_iotaW T hT i
  have hMb : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal := (hO.tuple ()).half.1
  have hp : T.Q.l.Mb * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := T.Q.l.prod
  have hp' : (∏ PP ∈ R.Pg, PP.asIdeal) * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by rw [← hMb]; exact hp
  have hM0 : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  have hu : ∀ P : R.Pg, IsUnit ((m : ℤ) : kP P.1) := fun P => isUnit_of_coprime hm (cast_res R.Pg hp' P.2)
  obtain ⟨z, hz⟩ := R.eG.surjective fun P => scalGL D.R.r (hu P)
  refine ⟨z, Subgroup.mem_center_iff.2 fun g => R.eG.injective ?_, fun a ha => ?_⟩
  · rw [R.eG.map_mul, R.eG.map_mul, hz]
    funext P
    exact scalGL_comm (hu P) (R.eG g P)
  · obtain ⟨k, hk, hf⟩ := hO.lift.lev z
    have hr := redFn_int (L := R.datWp i R.triv) (rank_Wc i) hk m
      (fun P => (congrArg Units.val (congrFun hz P)).trans (scalGL_val _ (hu P)))
    obtain ⟨w₃, hw₃, e₃⟩ := GlobalTheory.OneMapRef.Lift.cong_on_half hι (fun b hb => exists_cong_int (b := b) hβ R.Pg hp'
      (parLev_St hk.2.1) m hr hb) a ha
    obtain ⟨w₂, hw₂, e₂⟩ := hf a ha
    exact GlobalTheory.OneMapRef.Lift.sign_div hι hM0 (add_mem hw₂ hw₃) (int_calc e₂ e₃)

end GlobalTheory.GalCentral
