import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCommonSmulMem

noncomputable section

namespace GlobalTheory.Ker.MovLev

section Gen

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.AdLat.Translate
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (Af singleV)
open scoped TensorProduct Matrix Classical

theorem exists_mul_of_fg {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (P : Submonoid O)
    {L L' : Submodule O M} (hL : L.FG) (h : ∀ v ∈ L, ∃ s ∈ P, s • v ∈ L') :
    ∃ s ∈ P, ∀ v ∈ L, s • v ∈ L' := by
  first
  | exact @_root_.GlobalTheory.CommonSmulMembership.exists_common_smul_mem
  | exact _root_.GlobalTheory.CommonSmulMembership.exists_common_smul_mem
  | (apply _root_.GlobalTheory.CommonSmulMembership.exists_common_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonSmulMembership.exists_common_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonSmulMembership.exists_common_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonSmulMembership.exists_common_smul_mem ..)

variable {F : Type} [Field F] [NumberField F]

theorem mul_at (a b : Af F) (v : HeightOneSpectrum (𝓞 F)) : (a * b) v = a v * b v := rfl

theorem sub_at (a b : Af F) (v : HeightOneSpectrum (𝓞 F)) : (a - b) v = a v - b v := rfl

theorem one_at (v : HeightOneSpectrum (𝓞 F)) : (1 : Af F) v = 1 := rfl

def ofInt (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (h : ∀ v, x v ∈ v.adicCompletionIntegers F) :
    Af F := ⟨x, Filter.Eventually.of_forall h⟩

def idem (I : Ideal (𝓞 F)) : Af F :=
  ofInt (fun v => if I ≤ v.asIdeal then 1 else 0) fun v => by
    split_ifs
    exacts [one_mem _, zero_mem _]

theorem idem_at (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) :
    idem I v = if I ≤ v.asIdeal then 1 else 0 := rfl

theorem idem_int (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) : idem I v ∈ v.adicCompletionIntegers F := by
  rw [idem_at]
  split_ifs
  exacts [one_mem _, zero_mem _]

theorem idem_int' (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) :
    (1 - idem I) v ∈ v.adicCompletionIntegers F := sub_mem (one_mem _) (idem_int I v)

theorem val_coe (s : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (algebraMap F (Af F) (s : F) v) = v.intValuation s := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_of_algebraMap s

theorem coe_int (s : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    algebraMap F (Af F) (s : F) v ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, val_coe]
  exact v.intValuation_le_one s

theorem exists_clear (P : Submonoid (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F)
    (h : ∀ v, a v ∈ v.adicCompletionIntegers F ∨ ∃ s ∈ P, s ∈ v.asIdeal) :
    ∃ s ∈ P, ∀ v, (algebraMap F (Af F) (s : F) * a) v ∈ v.adicCompletionIntegers F := by
  have h1 : ∀ v, ∃ s ∈ P, (algebraMap F (Af F) (s : F) * a) v ∈ v.adicCompletionIntegers F := by
    intro v
    rcases h v with h | ⟨s, hs, hv⟩
    · exact ⟨1, one_mem _, mul_mem (coe_int 1 v) h⟩
    · by_cases h0 : Valued.v (a v) = 0
      · refine ⟨1, one_mem _, mul_mem (coe_int 1 v) ?_⟩
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h0.le.trans zero_le_one)
      · obtain ⟨n, hn⟩ := exists_pow_lt₀ ((v.intValuation_lt_one_iff_mem s).2 hv) (Units.mk0 _ h0)⁻¹
        refine ⟨s ^ n, pow_mem hs n, ?_⟩
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, mul_at, map_mul, val_coe, map_pow]
        rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hn
        exact (mul_le_mul_left hn.le _).trans (inv_mul_cancel₀ h0).le
  choose s hs hv using h1
  have hfin : {v | a v ∉ v.adicCompletionIntegers F}.Finite := Filter.eventually_cofinite.1 a.2
  refine ⟨∏ w ∈ hfin.toFinset, s w, prod_mem fun w _ => hs w, fun v => ?_⟩
  by_cases hw : v ∈ hfin.toFinset
  · rw [← Finset.prod_erase_mul _ _ hw]
    change (algebraMap F (Af F) (algebraMap (𝓞 F) F _) * a) v ∈ _
    rw [map_mul, map_mul, mul_assoc]
    exact mul_mem (coe_int _ v) (hv v)
  · exact mul_mem (coe_int _ v) (not_not.1 fun h => hw (hfin.mem_toFinset.2 h))

theorem single_same (v : HeightOneSpectrum (𝓞 F)) : singleV F v 1 v = 1 := RestrictedProduct.single_eq_same _ _ _

theorem single_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : singleV F v 1 w = 0 :=
  RestrictedProduct.single_eq_of_ne _ _ h

variable {E : Type} [Field E] [Algebra F E] {n : ℕ}

theorem kill (c : Af F) (x : RA F E) (h : ∀ v, c v = 0 ∨ algebraMap (Af F) (RA F E) (singleV F v 1) * x = 0) :
    algebraMap (Af F) (RA F E) c * x = 0 := by
  let B := Algebra.TensorProduct.basis (Af F) (Module.Free.chooseBasis F E)
  simp only [← Algebra.smul_def] at h ⊢
  refine B.ext_elem fun i => ?_
  rw [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul]
  refine FiniteAdeleRing.ext F fun v => ?_
  change c v * B.repr x i v = 0
  rcases h v with h | h
  · rw [h, zero_mul]
  · have h1 := congrArg (fun z => B.repr z i v) h
    simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, mul_at] at h1
    rw [single_same, one_mul] at h1
    rw [h1]; exact mul_zero _

theorem hat_int {S : Set (Fin n → E)} {a : Af F} (ha : ∀ v, a v ∈ v.adicCompletionIntegers F)
    {z : Fin n → RA F E} (hz : z ∈ hat F S) : algebraMap (Af F) (RA F E) a • z ∈ hat F S := hat_smul_int ha hz

variable [NumberField E]

theorem fv_int (s : 𝓞 F) (x : Fin n → E) : fv F (algebraMap (𝓞 F) (𝓞 E) s • x) =
    algebraMap (Af F) (RA F E) (algebraMap F (Af F) (s : F)) • fv F x := by
  funext i
  change (1 : Af F) ⊗ₜ[F] (algebraMap F E (s : F) * x i) =
    (algebraMap F (Af F) (s : F) ⊗ₜ[F] (1 : E)) * ((1 : Af F) ⊗ₜ[F] x i)
  rw [← Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.smul_tmul]

theorem exists_mul (P : Submonoid (𝓞 F)) (I : Ideal (𝓞 F))
    (hP : ∀ v : HeightOneSpectrum (𝓞 F), ¬ I ≤ v.asIdeal → ∃ s ∈ P, s ∈ v.asIdeal)
    {L Λ : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) (hΛ : Λ.FG) (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (h : ∀ z ∈ hat F (L : Set (Fin n → E)), algebraMap (Af F) (RA F E) (idem I) • z ∈ hat F (Λ : Set (Fin n → E))) :
    ∃ s ∈ P, ∀ v ∈ L, algebraMap (𝓞 F) (𝓞 E) s • v ∈ Λ := by
  obtain ⟨h1, -, -, h4⟩ := GlobalTheory.AdLat.hat_rational_points_and_approx F E n Λ hΛ hs
  obtain ⟨_, ⟨s, hs, rfl⟩, H⟩ := exists_mul_of_fg (P.map (algebraMap (𝓞 F) (𝓞 E))) (L' := Λ) hL fun x hx => by
    obtain ⟨d, hd, hx'⟩ := h4 (fv F x)
    obtain ⟨s, hs, hv⟩ := exists_clear P ((1 - idem I) * algebraMap F (Af F) (d : F)⁻¹) fun v => by
      by_cases hv : I ≤ v.asIdeal
      · left
        rw [mul_at, sub_at, idem_at, if_pos hv, one_at, sub_self, zero_mul]
        exact zero_mem _
      · exact Or.inr (hP v hv)
    refine ⟨_, ⟨s, hs, rfl⟩, (h1 _).1 ?_⟩
    rw [fv_int]
    have e := add_mem (hat_int (coe_int s) (h _ (fv_mem_hat hx))) (hat_int hv hx')
    convert e using 1
    have hd' : (d : F) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    have hd2 : algebraMap (Af F) (RA F E) (algebraMap F (Af F) (d : F)⁻¹) * (d : RA F E) = 1 := by
      rw [← map_natCast (algebraMap (Af F) (RA F E)), ← map_natCast (algebraMap F (Af F)), ← map_mul, ← map_mul,
        inv_mul_cancel₀ hd', map_one, map_one]
    rw [← Nat.cast_smul_eq_nsmul (RA F E), smul_smul, smul_smul, ← add_smul, map_mul, map_mul, mul_assoc, mul_assoc,
      hd2, map_sub, map_one]
    congr 1; ring
  exact ⟨s, hs, H⟩

theorem hat_mul {t : 𝓞 F} {L Λ : Submodule (𝓞 E) (Fin n → E)} (h : ∀ v ∈ L, algebraMap (𝓞 F) (𝓞 E) t • v ∈ Λ)
    {z : Fin n → RA F E} (hz : z ∈ hat F (L : Set (Fin n → E))) :
    algebraMap (Af F) (RA F E) (algebraMap F (Af F) (t : F)) • z ∈ hat F (Λ : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    rw [gen_eq, smul_comm, ← fv_int]
    exact hat_smul_int ha (fv_mem_hat (h x hx))
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem idem_mem (I : Ideal (𝓞 F)) {t : 𝓞 F} (ht : ∀ v : HeightOneSpectrum (𝓞 F), I ≤ v.asIdeal → t ∉ v.asIdeal)
    {L Λ : Submodule (𝓞 E) (Fin n → E)} (h : ∀ v ∈ L, algebraMap (𝓞 F) (𝓞 E) t • v ∈ Λ)
    {z : Fin n → RA F E} (hz : z ∈ hat F (L : Set (Fin n → E))) :
    algebraMap (Af F) (RA F E) (idem I) • z ∈ hat F (Λ : Set (Fin n → E)) := by
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 F), I ≤ v.asIdeal → Valued.v (algebraMap F (Af F) (t : F) v) = 1 :=
    fun v hv => by rw [val_coe]; exact v.intValuation_eq_one_iff.2 (ht v hv)
  have hb : ∀ v : HeightOneSpectrum (𝓞 F), (if I ≤ v.asIdeal then (algebraMap F (Af F) (t : F) v)⁻¹ else 0) ∈
      v.adicCompletionIntegers F := fun v => by
    split_ifs with hv
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1 v hv, inv_one]
    · exact zero_mem _
  obtain ⟨b, hb1, hb2⟩ : ∃ b : Af F, (∀ v, b v ∈ v.adicCompletionIntegers F) ∧
      ∀ v, b v = if I ≤ v.asIdeal then (algebraMap F (Af F) (t : F) v)⁻¹ else 0 := ⟨ofInt _ hb, hb, fun _ => rfl⟩
  have e : idem I = b * algebraMap F (Af F) (t : F) := by
    refine FiniteAdeleRing.ext F fun v => ?_
    rw [mul_at, idem_at, hb2]
    split_ifs with hv
    · refine (inv_mul_cancel₀ fun h0 => ?_).symm
      have := hv1 v hv
      rw [h0, map_zero] at this
      exact zero_ne_one this
    · rw [zero_mul]
  rw [e, map_mul, mul_smul]
  exact hat_int hb1 (hat_mul h hz)

end Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Member (cF)
open GlobalTheory.AdLat (hermA sg latOf)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {k : ℕ}

abbrev lf (a : Af D.host.F) : AfE D := algebraMap (Af D.host.F) (AfE D) a

theorem smul_mulVec_of {R : Type} [CommRing R] (c : R) (N : Matrix (Fin k) (Fin k) R) (h : c • (N - 1) = 0)
    (u : Fin k → R) : c • (N *ᵥ u) = c • u := by
  rw [smul_sub, sub_eq_zero] at h
  rw [← Matrix.smul_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem smul_mulVec_eq (c : Af D.host.F) (N : Matrix (Fin k) (Fin k) (AE D))
    (h : ∀ v, c v = 0 ∨ ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (N - 1) i j = 0)
    (u : Fin k → AfE D) : lf c • (N.map (finPart D) *ᵥ u) = lf c • u := by
  have h1 : lf c • (N - 1).map (finPart D) = 0 := by
    ext i j
    refine kill c (finPart D ((N - 1) i j)) fun v => (h v).imp id fun H => ?_
    have := congrArg (finPart D) (H (pairA D.host.F 0 (singleV D.host.F v 1))
      ⟨_, rfl, single_same v, fun _ hv' => single_ne hv'⟩ i j)
    rw [map_mul, map_zero] at this
    exact this
  have h2 : (N - 1).map (finPart D) = N.map (finPart D) - 1 := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [h2] at h1
  exact smul_mulVec_of _ _ h1 u

theorem trivAt_fmt {V : HSp D} {I : Ideal (𝓞 D.host.F)} {g : GA D V} (h : TrivAt V I g) (u) :
    lf (idem I) • (fmt V g *ᵥ u) = lf (idem I) • u :=
  smul_mulVec_eq _ _ (fun v => by
    by_cases hv : I ≤ v.asIdeal
    · exact Or.inr (h v hv)
    · exact Or.inl (if_neg hv)) u

theorem trivAt_fmtC {V : HSp D} {I : Ideal (𝓞 D.host.F)} {g : GA D V} (h : TrivAt V I g) (u) :
    lf (idem I) • (fmtC V g *ᵥ u) = lf (idem I) • u :=
  smul_mulVec_eq _ _ (fun v => by
    by_cases hv : I ≤ v.asIdeal
    · refine Or.inr fun ε hε i j => ?_
      have := congrArg (cA D) (h v hv ε hε i j)
      rw [map_mul, map_zero, Matrix.sub_apply, map_sub] at this
      have e : cA D (algebraMap (AF D.host.F) (AE D) ε) = algebraMap (AF D.host.F) (AE D) ε := by
        change ε ⊗ₜ D.sp.cm.sig 1 = ε ⊗ₜ 1
        rw [map_one]
      have e' : cA D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
          (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by
        rw [Matrix.one_apply]
        split_ifs
        exacts [map_one _, map_zero _]
      rw [e, e'] at this
      exact this
    · exact Or.inl (if_neg hv)) u

theorem trivOff_fmt {V : HSp D} {I : Ideal (𝓞 D.host.F)} {g : GA D V} (h : TrivOff V I g) (u) :
    lf (1 - idem I) • (fmt V g *ᵥ u) = lf (1 - idem I) • u :=
  smul_mulVec_eq _ _ (fun v => by
    by_cases hv : I ≤ v.asIdeal
    · left
      rw [sub_at, idem_at, if_pos hv, one_at, sub_self]
    · exact Or.inr (h v hv)) u

theorem full_of_mov {g : GL (Fin k) (AfE D)} {Λ L : Lt D.host.E k} (hΛ : Λ.FG)
    (hs : Submodule.span D.host.E (Λ : Set (Fin k → D.host.E)) = ⊤) (hL : L.FG) (h : IsMov g.1 Λ L) :
    Submodule.span D.host.E (L : Set (Fin k → D.host.E)) = ⊤ :=
  (((GlobalTheory.Ker.isMov_laws D k Λ ⟨hΛ, hs⟩).2.2.2 g.1 g⁻¹.1 g.mul_inv).2 L hL h).1

theorem eq_latOf {g : GL (Fin k) (AfE D)} {Λ L : Lt D.host.E k} (hΛ : Λ.FG)
    (hs : Submodule.span D.host.E (Λ : Set (Fin k → D.host.E)) = ⊤) (hL : L.FG) (h : IsMov g.1 Λ L) (v) :
    v ∈ latOf D.host.F g.1 (Λ : Set (Fin k → D.host.E)) ↔ v ∈ L := by
  rw [← (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E k L hL (full_of_mov hΛ hs hL h)).1 v]
  exact ⟨fun ⟨u, hu, e⟩ => (h _).2 ⟨u, hu, e.symm⟩, fun H => let ⟨u, hu, e⟩ := (h _).1 H; ⟨u, hu, e.symm⟩⟩

theorem agree_of_mov (P : Submonoid (𝓞 D.host.F)) (I : Ideal (𝓞 D.host.F))
    (hP : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ¬ I ≤ v.asIdeal → ∃ s ∈ P, s ∈ v.asIdeal)
    {g : GL (Fin k) (AfE D)} {Λ L : Lt D.host.E k} (hΛ : Λ.FG)
    (hs : Submodule.span D.host.E (Λ : Set (Fin k → D.host.E)) = ⊤) (hL : L.FG) (h : IsMov g.1 Λ L)
    (ht : ∀ u, lf (idem I) • (g.1 *ᵥ u) = lf (idem I) • u) :
    ∃ s ∈ P, (∀ v ∈ L, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s • v ∈ Λ) ∧
      ∀ v ∈ Λ, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s • v ∈ L := by
  obtain ⟨s, hsP, h1⟩ := exists_mul P I hP hL hΛ hs fun z hz => by
    obtain ⟨u, hu, rfl⟩ := (h z).1 hz
    have := ht u
    change lf (idem I) • (g.1 *ᵥ u) ∈ _
    rw [this]
    exact hat_int (idem_int I) hu
  obtain ⟨t, htP, h2⟩ := exists_mul P I hP hΛ hL (full_of_mov hΛ hs hL h) fun z hz => by
    change lf (idem I) • z ∈ _
    rw [← ht z]
    exact hat_int (idem_int I) ((h _).2 ⟨z, hz, rfl⟩)
  refine ⟨s * t, mul_mem hsP htP, fun v hv => ?_, fun v hv => ?_⟩
  · rw [map_mul, mul_comm, mul_smul]; exact Λ.smul_mem _ (h1 v hv)
  · rw [map_mul, mul_smul]; exact L.smul_mem _ (h2 v hv)

theorem mov_left {m₁ m₂ : Matrix (Fin k) (Fin k) (AfE D)} {Λ L : Lt D.host.E k} {I : Ideal (𝓞 D.host.F)}
    (h : IsMov (m₁ * m₂) Λ L) (h₁ : ∀ u, lf (idem I) • (m₁ *ᵥ u) = lf (idem I) • u)
    (h₂ : ∀ u, lf (1 - idem I) • (m₂ *ᵥ u) = lf (1 - idem I) • u)
    (a : ∀ z ∈ hatV L, lf (idem I) • z ∈ hatV Λ) (b : ∀ z ∈ hatV Λ, lf (idem I) • z ∈ hatV L) : IsMov m₁ Λ L := by
  have d (z : Fin k → AfE D) : lf (idem I) • z + lf (1 - idem I) • z = z := by
    rw [← add_smul, ← map_add, add_sub_cancel, map_one, one_smul]
  have key (u : Fin k → AfE D) : lf (1 - idem I) • (m₁ *ᵥ u) = lf (1 - idem I) • ((m₁ * m₂) *ᵥ u) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, h₂]
  intro w
  constructor
  · intro hw
    obtain ⟨u, hu, e⟩ := (h w).1 hw
    refine ⟨lf (idem I) • w + lf (1 - idem I) • u, add_mem (a w hw) (hat_int (idem_int' I) hu), ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h₁, key, ← e, d]
  · rintro ⟨u, hu, rfl⟩
    rw [← d (m₁ *ᵥ u), h₁, key]
    exact add_mem (b u hu) (hat_int (idem_int' I) ((h _).2 ⟨u, hu, rfl⟩))

abbrev cf (D : D7) : AfE D →+* AfE D := (sg (Af D.host.F) (cF D)).toRingHom

theorem cf_cf (x : AfE D) : cf D (cf D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact congrArg (a ⊗ₜ[D.host.F] ·) (star_star x)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem fin_cA (x : AE D) : finPart D (cA D x) = cf D (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem hermA_one (x y : Fin k → AfE D) :
    hermA (cF D) (1 : Matrix (Fin k) (Fin k) D.host.E) x y = ∑ a, x a * cf D (y a) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, ← Algebra.TensorProduct.one_def, mul_one]; rfl
  · intro b _ hb
    rw [Matrix.one_apply_ne hb.symm, TensorProduct.tmul_zero, mul_zero, zero_mul]
  · exact fun h => (h (Finset.mem_univ a)).elim

theorem hermA_conj {m : Matrix (Fin k) (Fin k) (AfE D)}
    (h : ∀ x y, hermA (cF D) 1 (m *ᵥ x) (m *ᵥ y) = hermA (cF D) 1 x y) (x y) :
    hermA (cF D) 1 (m.map (cf D) *ᵥ x) (m.map (cf D) *ᵥ y) = hermA (cF D) 1 x y := by
  have e (x : Fin k → AfE D) (a) : (m.map (cf D) *ᵥ x) a = cf D ((m *ᵥ (cf D ∘ x)) a) := by
    rw [RingHom.map_mulVec]
    congr 1
    funext i
    exact (cf_cf _).symm
  have := congrArg (cf D) (h (cf D ∘ x) (cf D ∘ y))
  simp only [hermA_one, map_sum, map_mul, e, Function.comp_apply, cf_cf] at this ⊢
  exact this

variable {S T : HSp D}

theorem mem_Vset (C : Ctx S T) {M : ℕ} {h : GA D S} {Λ : Lt D.host.E S.rank}
    (ht : TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h) (hΛ : Λ.FG) (hm : IsMov (fmtC S h) (stdL D.host.E S.rank) Λ) :
    Λ ∈ Vset D.host.E S.rank M := by
  let g : GL (Fin S.rank) (AfE D) := Matrix.GeneralLinearGroup.map (cf D) (finHom S h)
  have hg : g.1 = fmtC S h := by
    ext i j
    exact (fin_cA (mt S h i j)).symm
  obtain ⟨hfg, hsd, -⟩ := Base.stdL_mem_Vset (E := D.host.E) S.rank M
  have hs : Submodule.span D.host.E (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) = ⊤ := by
    rw [stdL, Submodule.span_span_of_tower, ← (Pi.basisFun D.host.E (Fin S.rank)).span_eq]
    congr 2
    funext i
    simp
  rw [← hg] at hm
  have hint (z : D.host.E) : z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔ IsIntegral ℤ z := by
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  refine ⟨hΛ, fun x => ?_, ?_⟩
  · have hu := (GlobalTheory.T.finitePart_preserves_form_det_norm_one D S h).1
    rw [show S.gramᵀ = 1 by rw [C.m.gS, Matrix.transpose_one]] at hu
    have key := GlobalTheory.AdLat.latOf_selfDual D.host.F D.host.E S.rank (stdL D.host.E S.rank) (cF D) 1 1 g hfg hs
      (fun x => star_star x) (fun a b => by
        rw [Matrix.one_apply, Matrix.one_apply, apply_ite (cF D), map_one, map_zero]
        exact if_congr eq_comm rfl rfl) (by simp) one_ne_zero
      (fun v => by simp only [hint]; exact (hsd v).symm) (hermA_conj hu) x
    simp only [hint, eq_latOf hfg hs hΛ hm] at key
    exact key.symm
  · let P : Submonoid (𝓞 D.host.F) :=
      { carrier := {s | ∃ n : ℕ, 0 < n ∧ n.Coprime M ∧ s = n}
        one_mem' := ⟨1, one_pos, Nat.coprime_one_left M, Nat.cast_one.symm⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, ha', rfl⟩ ⟨b, hb, hb', rfl⟩
          exact ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', (Nat.cast_mul a b).symm⟩ }
    obtain ⟨_, ⟨s, hs0, hsM, rfl⟩, h1, h2⟩ := agree_of_mov P (Ideal.span {(M : 𝓞 D.host.F)}) (fun v hv => by
      haveI := v.isPrime
      obtain ⟨p, hp, e⟩ := (Ideal.isPrime_int_iff.mp (Ideal.IsPrime.under ℤ v.asIdeal)).resolve_left
        (Ideal.under_ne_bot ℤ v.ne_bot)
      have hpv : (p : 𝓞 D.host.F) ∈ v.asIdeal := by
        have : (p : ℤ) ∈ v.asIdeal.under ℤ := e ▸ Ideal.mem_span_singleton_self _
        simpa using this
      refine ⟨p, ⟨p, hp.pos, (Nat.Prime.coprime_iff_not_dvd hp).2 ?_, rfl⟩, hpv⟩
      rintro ⟨c, rfl⟩
      refine hv ((Ideal.span_singleton_le_iff_mem _).2 ?_)
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hpv) hfg hs hΛ hm (hg ▸ trivAt_fmtC ht)
    rw [map_natCast] at h1 h2
    exact ⟨s, hs0, hsM, h1, h2⟩

theorem selfD_of_mov (C : Ctx S T) {g : GA D T} {L : Lt D.host.E T.rank} (hL : L.FG)
    (hm : IsMov (fmt T g) C.X.Λ L) : SelfD C.X L := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D T
  have hE (x y : Fin T.rank → D.host.E) : EF C.X x y =
      -Algebra.trace ℚ D.host.E (D.host.xi0 * ∑ a, ∑ b, x a * T.gramᵀ a b * cF D (y b)) := by
    rw [EF_def, C.m.ka, C.m.gT, mul_div_cancel_left₀ _ two_ne_zero, neg_mul, map_neg]
    rfl
  have hJ (Λ : Lt D.host.E T.rank) (x : Fin T.rank → D.host.E) :
      (∀ y ∈ Λ, (∑ a, ∑ b, x a * T.gramᵀ a b * cF D (y b)) ∈ D.host.AA * D.host.AAbar) ↔
        ∀ y ∈ Λ, ∃ k : ℤ, EF C.X x y = k := by
    constructor
    · intro H y hy
      obtain ⟨n, hn⟩ := trace_int_of_mem Formalism.IndefR.Fin.factPrincipalDatum D (H y hy)
      exact ⟨-n, by rw [hE, hn, Int.cast_neg]⟩
    · intro H y hy
      refine (GlobalTheory.Member.LatSelfDual.mem_iff_trace D _).2 fun a => ?_
      obtain ⟨n, hn⟩ := H _ (Λ.smul_mem (Lev.bar a) hy)
      rw [← Lev.EF_smul, hE] at hn
      refine ⟨-n, ?_⟩
      rw [Int.cast_neg, ← hn, neg_neg]
      exact congrArg (fun z => Algebra.trace ℚ D.host.E (D.host.xi0 * z))
        (GlobalTheory.Member.LatSelfDual.frameForm_smul_left T a x y).symm
  refine ⟨hL, fun x => ?_⟩
  have key := GlobalTheory.AdLat.latOf_selfDual D.host.F D.host.E T.rank C.X.Λ (cF D) T.gramᵀ
    (D.host.AA * D.host.AAbar) (finHom T g) C.X.Λ_fg C.X.Λ_span hcc hG hdet
    (mul_ne_zero (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D))
    (fun v => (hJ _ v).trans ((Lev.selfD_of_sympl C.sympl).2 v).symm) (GlobalTheory.T.finitePart_preserves_form_det_norm_one D T g).1 x
  simp only [eq_latOf (g := finHom T g) C.X.Λ_fg C.X.Λ_span hL hm] at key
  exact key.symm.trans (hJ L x)

theorem bar_algebraMap (s : 𝓞 D.host.F) :
    Lev.bar (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s :=
  (IsCMField.ringOfIntegersComplexConj D.host.E).commutes s

theorem mem_lats (C : Ctx S T) (Lv : SW.Level C.X) {g : GA D T} {L : Lt D.host.E T.rank} (hL : L.FG)
    (hm : IsMov (fmt T g) C.X.Λ L) (ht : TrivAt T (C.under Lv) g) : L ∈ Lv.lats := by
  let P : Submonoid (𝓞 D.host.F) :=
    { carrier := {s | IsCoprime (Ideal.span {s}) (C.under Lv)}
      one_mem' := Lev.cop_one
      mul_mem' := Lev.cop_mul }
  obtain ⟨s, hs, h1, h2⟩ := agree_of_mov (g := finHom T g) P (C.under Lv) (fun v hv => by
    obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 hv
    obtain ⟨y, i, hi, e⟩ := v.isMaximal.exists_inv ha'
    exact ⟨i, Lev.cop_iff.2 ⟨1, y * a, Ideal.mul_mem_left _ _ ha, by linear_combination e⟩, hi⟩)
    C.X.Λ_fg C.X.Λ_span hL hm (trivAt_fmt ht)
  refine ⟨selfD_of_mov C hL hm, _, ?_, h1, h2⟩
  obtain ⟨a, m, hm, e⟩ := Lev.cop_iff.1 hs
  have e' := congrArg (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) e
  rw [map_add, map_mul, map_one] at e'
  exact IsCoprime.mul_right (Lev.cop_iff.2 ⟨_, _, hm, e'⟩)
    (Lev.cop_iff.2 ⟨_, _, Lev.mem_conjI.2 (by rw [bar_algebraMap]; exact hm), e'⟩)

theorem exists_triv (C : Ctx S T) (Lv : SW.Level C.X) {g : GA D T} {L : Lt D.host.E T.rank}
    (hm : IsMov (fmt T g) C.X.Λ L) (hL : L ∈ Lv.lats) :
    ∃ g' ∈ GfC T, TrivAt T (C.under Lv) g' ∧ IsMov (fmt T g') C.X.Λ L := by
  obtain ⟨-, hmul, hsplit, hinf, hlev⟩ := (GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.2.2 T
  obtain ⟨a, ha, f, hf, rfl⟩ := hsplit g
  obtain ⟨f₁, hf₁, f₂, -, rfl, -, t₁, t₂⟩ := hlev (C.under Lv) (Ideal.under_ne_bot _ Lv.ne_bot) f hf
  rw [(hmul _ _).2.1, (hinf a ha).1, one_mul, (hmul _ _).2.1] at hm
  obtain ⟨-, s, hs, h1, h2⟩ := hL
  obtain ⟨t, ht⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E (Lev.bar s * s)).1 (by
    change Lev.bar _ = _
    rw [map_mul, Lev.bar_bar, mul_comm])
  have ht' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = Lev.bar s * s := ht
  have hc : IsCoprime (Ideal.span {Lev.bar s * s}) Lv.𝔪 := by
    refine Lev.cop_mul ?_ hs.of_mul_right_left
    obtain ⟨b, m, hm', e⟩ := Lev.cop_iff.1 hs.of_mul_right_right
    exact Lev.cop_iff.2 ⟨Lev.bar b, Lev.bar m, Lev.mem_conjI.1 hm', by rw [← map_mul, ← map_add, e, map_one]⟩
  have hv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), C.under Lv ≤ v.asIdeal → t ∉ v.asIdeal := fun v hv htv => by
    haveI := v.isPrime
    obtain ⟨Q, hQ, hQp, e⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal Lv.𝔪 hv
    obtain ⟨b, m, hm', e'⟩ := Lev.cop_iff.1 hc
    rw [← e, Ideal.mem_comap, ht'] at htv
    exact hQp.ne_top ((Ideal.eq_top_iff_one _).2 (e' ▸ add_mem (Ideal.mul_mem_left _ _ htv) (hQ hm')))
  refine ⟨f₁, hf₁, t₁, mov_left hm (trivAt_fmt t₁) (trivOff_fmt t₂) (fun z hz => idem_mem _ hv (fun v hv => ?_) hz)
    fun z hz => idem_mem _ hv (fun v hv => ?_) hz⟩
  · rw [ht', mul_smul]; exact C.X.Λ.smul_mem _ (h1 v hv)
  · rw [ht', mul_smul]; exact L.smul_mem _ (h2 v hv)

theorem mov_mem_lattices : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∀ (M : ℕ) (h : GA D S) (Λ : Lt D.host.E S.rank), 0 < M → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → Λ ∈ Vset D.host.E S.rank M) ∧ ∀ (Lv : SW.Level C.X) (g : GA D T) (L : Lt D.host.E T.rank), L.FG → IsMov (fmt T g) C.X.Λ L → SelfD C.X L ∧ (TrivAt T (C.under Lv) g → L ∈ Lv.lats) ∧ C.under Lv ≠ ⊥ ∧ (L ∈ Lv.lats → ∃ g' ∈ GfC T, TrivAt T (C.under Lv) g' ∧ IsMov (fmt T g') C.X.Λ L) :=
  fun _ _ _ C => ⟨fun _ _ _ _ ht hΛ hm => mem_Vset C ht hΛ hm, fun Lv _ _ hL hm =>
    ⟨selfD_of_mov C hL hm, mem_lats C Lv hL hm, Ideal.under_ne_bot _ Lv.ne_bot, exists_triv C Lv hm⟩⟩

end GlobalTheory.Ker.MovLev

end
