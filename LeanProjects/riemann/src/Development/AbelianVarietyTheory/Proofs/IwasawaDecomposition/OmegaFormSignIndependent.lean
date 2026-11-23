import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateModelSameThetaFunctions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFinitePointMovesVacuumToProjectionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormPeriodRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicThetaOfTestFunctionExistsLawsFockVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionFixesLevelVectorUpToUnit
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HostElementIdempotentModTwo
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RdUEqConstMulClsSum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.Term

open GlobalTheory.Ker GlobalTheory.TensLatMove

variable {D : D7} {S T : HSp D}

theorem exists_half {R W A : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup A] (B : W →+ W →+ A)
    (c : R → R) (hc : ∀ a p q, B (a • p) q = B p (c a • q)) (K : AddSubgroup A) {H : AddSubgroup W}
    (hH : ∀ u ∈ H, ∀ u' ∈ H, B u u' ∈ K) {σ τ : R} {k M : ℕ} (h1 : σ + (2 * k * k : ℕ) * τ = 1)
    (hτ : ∀ u ∈ H, τ • u ∈ H) {x y : W}
    (hk : k • (x - y) ∈ H) (hM : k • M • y ∈ H) (hx : ∃ u ∈ H, σ • x = 2 • u) (hy : ∃ u ∈ H, σ • y = 2 • u)
    (hx' : ∃ u ∈ H, c τ • x = (2 * M) • u) (hy' : ∃ u ∈ H, k • c τ • y = (2 * M) • u) :
    ∃ u ∈ H, x = y + 2 • u ∧ B y u ∈ K := by
  obtain ⟨a, ha, ea⟩ := hx
  obtain ⟨b, hb, eb⟩ := hy
  obtain ⟨a', ha', ec⟩ := hx'
  obtain ⟨d, hd, ed⟩ := hy'
  have dec (z : W) : z = σ • z + (2 * k * k) • τ • z := by
    rw [← Nat.cast_smul_eq_nsmul R, smul_smul, ← add_smul, h1, one_smul]
  have hu : a - b + k • τ • k • (x - y) ∈ H := add_mem (sub_mem ha hb) (nsmul_mem (hτ _ hk) _)
  have e : x - y = 2 • (a - b + k • τ • k • (x - y)) := by
    conv_lhs => rw [dec (x - y), smul_sub, ea, eb]
    rw [smul_comm τ k, smul_add, smul_sub 2, smul_smul 2, smul_smul (2 * k)]
  generalize a - b + k • τ • k • (x - y) = u at hu e
  refine ⟨u, hu, by rw [← e, add_sub_cancel], ?_⟩
  have nl (n : ℕ) (p q : W) : B (n • p) q = B p (n • q) := by
    rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply]
  have e2 : B ((2 * k * k) • τ • y) u = B (k • M • y) (2 • (k • a' - d)) := by
    have e3 : k • c τ • (2 • u) = M • 2 • (k • a' - d) := by
      rw [← e, smul_sub, smul_sub, ec, ed, smul_comm k, ← smul_sub, smul_smul M, mul_comm M]
    rw [nl k, nl M, smul_comm M k, ← e3, nl, hc, smul_comm (c τ), smul_comm (c τ), smul_smul k, smul_smul]
    congr 2
    ring
  rw [dec y, map_add, AddMonoidHom.add_apply, eb, e2]
  exact add_mem (hH _ (nsmul_mem hb 2) _ hu) (hH _ hM _ (nsmul_mem (sub_mem (nsmul_mem ha' k) hd) 2))

theorem heis_congr {ψ : AddChar (AF D.host.F) ℂ} {H : AddSubgroup (WO S T)}
    (hH : ∀ u ∈ H, ∀ u' ∈ H, ψ (symplO S T u u') = 1) {f : WO S T → ℂ} (hf : ∀ u ∈ H, heisO ψ S T (2 • u) f = f)
    {σ τ : Formalism.L2.Theta.AE D} {k M : ℕ} (h1 : σ + (2 * k * k : ℕ) * τ = 1) (hτ : ∀ u ∈ H, τ • u ∈ H) {x y : WO S T}
    (hk : k • (x - y) ∈ H) (hM : k • M • y ∈ H) (hx : ∃ u ∈ H, σ • x = 2 • u) (hy : ∃ u ∈ H, σ • y = 2 • u)
    (hx' : ∃ u ∈ H, cA D τ • x = (2 * M) • u) (hy' : ∃ u ∈ H, k • cA D τ • y = (2 * M) • u) :
    heisO ψ S T x f = heisO ψ S T y f := by
  obtain ⟨u, hu, rfl, hp⟩ := exists_half (LatVac.symplHom S T) (cA D) (SplitScalar.symplO_smul S T)
    (LatVac.kerChar ψ) hH h1 hτ hk hM hx hy hx' hy'
  have hp' : ψ (symplOH S T y (2 • u)) = 1 := by
    rw [two_nsmul, SplitScalar.symplOH_add_right, SplitScalar.symplOH_add_self]
    exact hp
  have := SplitScalar.heisO_heisO ψ S T y (2 • u) f
  rw [hf u hu, hp', one_smul] at this
  exact this.symm

theorem exists_split {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) {k : ℕ} (hk : Nat.Coprime k l.M) (j : ℕ) :
    ∃ s ∈ l.Mb ^ j, ∃ t : 𝓞 D.host.E, H.bar t ∈ l.Mb ^ j ∧ s + (2 * k * k : ℕ) * t = 1 := by
  have hM : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
    have hMM : (l.M : 𝓞 D.host.E) ∈ l.Mb * Mfr l := l.prod.ge (Ideal.subset_span rfl)
    exact Ideal.mul_le_left hMM
  have c1 : IsCoprime l.Mb (Mfr l) := Ideal.isCoprime_iff_sup_eq.2 l.coprime
  have c2 : IsCoprime l.Mb (Ideal.span {((2 * k * k : ℕ) : 𝓞 D.host.E)}) := by
    have h2 : Nat.Coprime (2 * k * k) l.M :=
      Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.coprime_two_left.2 l.odd) hk) hk
    obtain ⟨a, b, e⟩ : IsCoprime ((2 * k * k : ℕ) : 𝓞 D.host.E) (l.M : 𝓞 D.host.E) := h2.cast
    exact Ideal.isCoprime_iff_exists.2 ⟨_, l.Mb.mul_mem_left b hM, _, Ideal.mem_span_singleton'.2 ⟨a, rfl⟩,
      (add_comm _ _).trans e⟩
  obtain ⟨s, hs, t, ht, e⟩ := Ideal.isCoprime_iff_exists.1 ((c2.mul_right (c1.pow_right (n := j))).pow_left (m := j))
  obtain ⟨t', ht', rfl⟩ := Ideal.mem_span_singleton_mul.1 ht
  refine ⟨s, hs, t', ?_, e⟩
  have h1 : (Mfr l ^ j).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ l.Mb ^ j := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun a ha => LevelPairing.bar_mem_Mb ha) j
  exact h1 (Ideal.mem_map_of_mem _ ht')

theorem smul_mem_of_int {Λ : Lt D.host.E S.rank} (hΛ : Λ ∈ Vset D.host.E S.rank 1) {L : Lt D.host.E T.rank}
    {a : Formalism.L2.Theta.AE D} (ha : finPart D a ∈ Formalism.L2.Theta.intAE D) {u : WO S T} (hu : u ∈ hatA S T (tens Λ L)) :
    a • u ∈ hatA S T (tens Λ L) ∧ cA D a • u ∈ hatA S T (tens Λ L) := by
  have hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens Λ L, (o : D.host.E) • y ∈ tens Λ L := fun o y hy =>
    TensLat.smul_mem_tens hΛ o.isIntegral_coe hy
  have h1 : ∀ z ∈ Formalism.L2.Theta.intAE D, emb D z ∈ SignVac.intAE D ∧ cA D (emb D z) ∈ SignVac.intAE D := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, hα, o, rfl⟩ := hz
      exact ⟨AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩, AddSubgroup.subset_closure
        ⟨α, hα, ⟨cc (o : D.host.E), Base.isIntegral_cc o.isIntegral_coe⟩, rfl⟩⟩
    | zero => rw [map_zero, map_zero]; exact ⟨zero_mem _, zero_mem _⟩
    | add x y _ _ hx hy => rw [map_add, RingHom.map_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | neg x _ hx => rw [map_neg, RingHom.map_neg]; exact ⟨neg_mem hx.1, neg_mem hx.2⟩
  have h2 := emb_mul a 1
  rw [mul_one] at h2
  have h3 : emb D 1 = pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  have h4 : cA D (emb D 1) = emb D 1 := by
    rw [h3]
    exact congrArg (fun t => pairA D.host.F 0 1 ⊗ₜ[D.host.F] t) (star_one D.host.E)
  have h5 := h1 _ ha
  rw [h2, RingHom.map_mul, h4, h3] at h5
  rw [← SignVac.one_smul_hatA hu, smul_smul, smul_smul]
  exact ⟨SignVac.smul_mem_hatA hA h5.1 hu, SignVac.smul_mem_hatA hA h5.2 hu⟩

noncomputable def colM (S T : HSp D) : (Fin S.rank → Fin T.rank → AfE D) →+ WO S T :=
  AddMonoidHom.mk' (fun u => Matrix.of fun a k => emb D (u k a)) fun _ _ => by
    ext a k
    exact map_add (emb D) _ _

theorem finW_eq_colM (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : finW S T y = colM S T fun b => toAf (y b) := rfl

theorem colM_mem {L : Lt D.host.E T.rank} {u : Fin S.rank → Fin T.rank → AfE D} (hu : ∀ b, u b ∈ hatV L) :
    colM S T u ∈ hatA S T (tens (stdL D.host.E S.rank) L) := by
  rw [← Finset.univ_sum_single u, map_sum]
  refine sum_mem fun b _ => ?_
  have h1 : (Pi.single b 1 : Fin S.rank → D.host.E) ∈ stdL D.host.E S.rank := Submodule.subset_span ⟨b, rfl⟩
  refine (congrArg (· ∈ hatA S T (tens (stdL D.host.E S.rank) L)) ?_).mpr
    (outer_mem S T _ L _ (LevEig.toAf_mem h1) _ (hu b))
  ext a k
  change emb D ((Pi.single b (u b) : Fin S.rank → Fin T.rank → AfE D) k a) = emb D (u b a * toAf (Pi.single b 1) k)
  by_cases e : k = b
  · subst e
    simp only [toAf, Pi.single_eq_same]
    exact congrArg (emb D) (mul_one _).symm
  · simp only [toAf, Pi.single_eq_of_ne e, TensorProduct.tmul_zero, mul_zero, Pi.zero_apply]

theorem actO_colM (g : GA D T) (u : Fin S.rank → Fin T.rank → AfE D) :
    actO S T 1 g (colM S T u) = colM S T fun b => fmt T g *ᵥ u b := by
  have e : Formalism.L2.Theta.mt S 1⁻¹ = 1 := by rw [inv_one, Formalism.L2.Theta.mt, map_one, Units.val_one]
  rw [actO, e, Matrix.mul_one]
  ext a k
  change ∑ c, Formalism.L2.Theta.mt T g a c * emb D (u k c) = emb D (∑ c, finPart D (Formalism.L2.Theta.mt T g a c) * u k c)
  rw [map_sum]
  exact Finset.sum_congr rfl fun c _ => (emb_mul _ _).symm

theorem inc_smul_finW (s : D.host.E) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    incA D s • finW S T y = finW S T (s • y) := by
  ext a k
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] s) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] y k a) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

theorem finW_nsmul (n : ℕ) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : finW S T (n • y) = n • finW S T y := by
  rw [← Nat.cast_smul_eq_nsmul D.host.E, ← inc_smul_finW, map_natCast, Nat.cast_smul_eq_nsmul]

theorem finW_mem {L : Lt D.host.E T.rank} {y : Matrix (Fin S.rank) (Fin T.rank) D.host.E} (hy : ∀ b, y b ∈ L) :
    finW S T y ∈ hatA S T (tens (stdL D.host.E S.rank) L) := colM_mem fun b => LevEig.toAf_mem (hy b)

theorem nsmul_mem_of_le {Λ Λ' : Lt D.host.E S.rank} {L : Lt D.host.E T.rank} {n : ℕ}
    (h : Ideal.span {(n : 𝓞 D.host.E)} • Λ ≤ Λ') {u : WO S T} (hu : u ∈ hatA S T (tens Λ L)) :
    n • u ∈ hatA S T (tens Λ' L) := by
  refine hatA_le S T Λ L ((hatA S T (tens Λ' L)).comap (nsmulAddMonoidHom n)) (fun v hv w hw => ?_) hu
  change n • outerHom S T v w ∈ hatA S T (tens Λ' L)
  rw [← AddMonoidHom.nsmul_apply, ← map_nsmul]
  refine outer_mem S T Λ' L _ (AddSubgroup.closure_mono ?_
    (LevEig.nsmul_mem_hatV (Ideal.mem_span_singleton_self _) hv)) _ hw
  rintro z ⟨a, ha, x, hx, e⟩
  exact ⟨a, ha, x, h hx, e⟩

theorem isMov_latG (g : GA D T) : IsMov (fmt T g) (latG T 1) (latG T g) := by
  obtain ⟨-, -, -, h4, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D T g
  rw [h5] at h4
  intro u
  exact Iff.trans (Set.ext_iff.1 h4 u) ⟨fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩, fun ⟨y, hy, e⟩ => ⟨y, hy, e.symm⟩⟩

theorem actO_split (h : GA D S) (g : GA D T) (x : WO S T) : actO S T h g x = actO S T h 1 (actO S T 1 g x) := by
  simp only [actO, Formalism.L2.Theta.mt, inv_one, map_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]

theorem actO_smul (h : GA D S) (g : GA D T) (a : Formalism.L2.Theta.AE D) (x : WO S T) :
    actO S T h g (a • x) = a • actO S T h g x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

theorem actO_sub_self {e : Formalism.L2.Theta.AE D} {h : GA D S} (hs : SuppAt e S h) (x : WO S T) :
    actO S T h 1 x - x = actO S T h 1 ((e + cA D e) • x) - (e + cA D e) • x := by
  have h1 : (e + cA D e) • (Formalism.L2.Theta.mt S h - 1) = Formalism.L2.Theta.mt S h - 1 := Matrix.ext hs
  have h2 : Formalism.L2.Theta.mt S h⁻¹ * Formalism.L2.Theta.mt S h = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv, Units.inv_mul]
  have gen : ∀ {R : Type} [CommRing R] (ε : R) (A B : Matrix (Fin S.rank) (Fin S.rank) R)
      (z : Matrix (Fin T.rank) (Fin S.rank) R), ε • (A - 1) = A - 1 → B * A = 1 →
      z * B - z = (ε • z) * B - ε • z := by
    intro R _ ε A B z h1 h2
    have h3 (w : Matrix (Fin T.rank) (Fin S.rank) R) : w * B - w = -(w * B * (A - 1)) := by
      rw [Matrix.mul_sub, Matrix.mul_assoc w B A, h2, Matrix.mul_one, Matrix.mul_one, neg_sub]
    rw [h3, h3, Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_smul, h1]
  have h0 : Formalism.L2.Theta.mt T 1 = 1 := by rw [Formalism.L2.Theta.mt, map_one, Units.val_one]
  rw [actO, actO, h0, Matrix.one_mul, Matrix.one_mul]
  exact gen _ _ _ _ h1 h2

section Rows

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem modN_of_both {a : Dw.La} (h1 : a ∈ (Mfr l • ⊤ : Submodule (𝓞 D.host.E) Dw.La))
    (h2 : a ∈ (l.Mb • ⊤ : Submodule (𝓞 D.host.E) Dw.La)) : ∃ b, a = l.M • b := by
  obtain ⟨b, hb⟩ := DualMark.smul_eq_nsmul (DualMark.prod_le l) (LevelPairing.cSep_spec l).2 h1
  obtain ⟨b', hb'⟩ := DualMark.smul_eq_nsmul ((mul_comm _ _).le.trans (DualMark.prod_le l))
    (LevelPairing.cSep_spec l).1 h2
  exact ⟨b' - b, by rw [smul_sub, ← hb, ← hb', sub_smul, one_smul, sub_sub_cancel]⟩

theorem inv_smul_nsmul {r : ℕ} (v : Fin r → D.host.E) : (l.M : D.host.E)⁻¹ • l.M • v = v := by
  rw [← Nat.cast_smul_eq_nsmul D.host.E, inv_smul_smul₀ (Nat.cast_ne_zero.2 (DualMark.level_ne l))]

theorem nsmul_root_mem {r : ℕ} {L : Lt D.host.E r} {mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)} (hmk : ∀ a, mk a ∈ L)
    {a : Dw.La} (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) {y : Fin r → D.host.E}
    (hy : y - (l.M : D.host.E)⁻¹ • mk a ∈ L) {B : ℕ}
    (hB : (B : 𝓞 D.host.E) • (Submodule.Quotient.mk a : LevQ Dw l) = 0) : B • y ∈ L := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hB
  obtain ⟨c, hc⟩ := modN_of_both (Submodule.smul_mem _ _ ha) hB
  rw [Nat.cast_smul_eq_nsmul] at hc
  have := add_mem (nsmul_mem hy B) (hmk c)
  rwa [smul_sub, smul_comm B, ← map_nsmul, hc, map_nsmul, inv_smul_nsmul, sub_add_cancel] at this

theorem root_cong {g : GA D T} {ι mk : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)} (hι : ∀ a, ι a ∈ latG T 1)
    (hm : MarkAd (T := T) rfl l ι g mk) {a a₀ : Dw.La} (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La))
    (ha₀ : a₀ ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La))
    (e : (Submodule.Quotient.mk a₀ : LevQ Dw l) = Submodule.Quotient.mk a) {y y₀ : Fin T.rank → D.host.E}
    (hy : y - (l.M : D.host.E)⁻¹ • mk a ∈ latG T g) (hy₀ : y₀ - (l.M : D.host.E)⁻¹ • ι a₀ ∈ latG T 1) :
    fmt T g *ᵥ toAf y₀ - toAf y ∈ hatV (latG T g) := by
  obtain ⟨c, hc⟩ := modN_of_both (sub_mem ha₀ ha) ((Submodule.Quotient.eq _).1 e)
  have h0 : y₀ - (l.M : D.host.E)⁻¹ • ι a ∈ latG T 1 := by
    have := add_mem hy₀ (hι c)
    rwa [eq_add_of_sub_eq hc, map_add, map_nsmul, smul_add, inv_smul_nsmul, ← sub_sub, sub_add_eq_add_sub,
      sub_add_cancel] at this
  obtain ⟨w, hw, ew⟩ := hm a ha
  rw [(GlobalTheory.Member.latG_lattice_and_completion D T g).2.2.2.2.1] at hw
  replace ew : toAf (mk a) - fmt T g *ᵥ toAf (ι a) = l.M • w := ew
  set μ : AfE D := (1 : Af D.host.F) ⊗ₜ[D.host.F] (l.M : D.host.E)⁻¹ with hμ
  have t1 (v : Fin T.rank → D.host.E) : toAf ((l.M : D.host.E)⁻¹ • v) = μ • toAf v := by
    funext i
    simp only [toAf, hμ, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have t2 : μ * (l.M : AfE D) = 1 := by
    rw [hμ, ← map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E)),
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (DualMark.level_ne l))]
    rfl
  have h1 := (isMov_latG g _).2 ⟨_, LevEig.toAf_mem h0, rfl⟩
  have h2 := LevEig.toAf_mem hy
  rw [LevEig.toAf_sub, t1] at h1 h2
  have gen : ∀ {R : Type} [CommRing R] (A : Matrix (Fin T.rank) (Fin T.rank) R) (μ : R) (M : ℕ)
      (p q s t w : Fin T.rank → R), μ * M = 1 → t - A *ᵥ s = M • w →
      A *ᵥ p - q = A *ᵥ (p - μ • s) - (q - μ • t) - w := by
    intro R _ A μ M p q s t w h1 h2
    have : w = μ • (t - A *ᵥ s) := by rw [h2, ← Nat.cast_smul_eq_nsmul R, smul_smul, h1, one_smul]
    rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub]
    abel
  rw [gen _ μ l.M _ _ _ _ w t2 ew]
  exact sub_mem (sub_mem h1 h2) hw

theorem exists_pow {n r N : ℕ} {L : Lt D.host.E r} {y : Matrix (Fin n) (Fin r) D.host.E}
    (h : ∀ b, ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ L, s • y b = (2 * N) • u) :
    ∃ j : ℕ, ∀ j' ≥ j, ∀ s ∈ l.Mb ^ j', ∃ u : Matrix (Fin n) (Fin r) D.host.E, (∀ b, u b ∈ L) ∧
      (s : D.host.E) • y = (2 * N) • u := by
  choose j hj using h
  refine ⟨Finset.univ.sup j, fun j' hj' s hs => ?_⟩
  choose u hu e using fun b => hj b s
    (Ideal.pow_le_pow_right ((Finset.le_sup (Finset.mem_univ b)).trans hj') hs)
  exact ⟨Matrix.of u, hu, funext e⟩

end Rows

theorem isMov_fmt_one (L : Lt D.host.E T.rank) : IsMov (fmt T 1) L L := fun v => by
  simp only [LevEig.fmt_one, Matrix.one_mulVec, exists_eq_right']

theorem heisG_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (y : Matrix (Fin n) (Fin r) E) (a : ℂ) (φ : TF n g) :
    heisG X bas y (a • φ) = a • heisG X bas y φ := by
  funext z
  simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem char_hatA (C : Ctx S T) {Λ : Lt D.host.E S.rank} (hΛ : Λ ∈ Vset D.host.E S.rank 1) {L : Lt D.host.E T.rank}
    (hL : SelfD C.X L) : ∀ u ∈ hatA S T (tens Λ L), ∀ u' ∈ hatA S T (tens Λ L), C.ψ (symplO S T u u') = 1 := by
  have hA : ∀ o : 𝓞 D.host.E, ∀ y ∈ tens Λ L, (o : D.host.E) • y ∈ tens Λ L := fun o y hy =>
    TensLat.smul_mem_tens hΛ o.isIntegral_coe hy
  refine fun u hu u' hu' => SignVac.char_sympl_hatA C.std.1.1 hA (fun y hy y' hy' => ?_) hu hu'
  obtain ⟨k, hk⟩ := (TensLat.tens_selfDual hΛ hL y).1 hy y' hy'
  rw [← SplitScalar.symplOH_add_self, AddChar.map_add_eq_mul, (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.2.1, hk, ← Complex.exp_add,
    ← Complex.exp_int_mul_two_pi_mul_I (-k)]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 1600000 in

theorem heis_root (C : Ctx S T) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {h : GA D S} {g : GA D T} {Λ : Lt D.host.E S.rank} (hΛ : Λ ∈ Vset D.host.E S.rank 1)
    (hmv : IsMov (fmtC S h) (stdL D.host.E S.rank) Λ) (hL : SelfD C.X (latG T g)) {f : WO S T → ℂ}
    (hf : ∀ u ∈ hatA S T (tens Λ (latG T g)), heisO C.ψ S T (2 • u) f = f)
    {ι mk : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)} (hι : ∀ a, ι a ∈ latG T 1) (hmk : ∀ a, mk a ∈ latG T g)
    (hm : MarkAd (T := T) rfl l ι g mk) {N k B : ℕ} (hN : l.M ∣ N)
    (hN' : Ideal.span {(N : 𝓞 D.host.E)} • stdL D.host.E S.rank ≤ Λ) (hk : Nat.Coprime k l.M)
    (hk' : Ideal.span {(k : 𝓞 D.host.E)} • stdL D.host.E S.rank ≤ Λ) (hB : B ≠ 0) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (hP : ∀ PP ∈ P, (B : 𝓞 D.host.E) ∉ PP.asIdeal) (hs : SuppAt e S h)
    {Y₀ Y : (Fin S.rank → LevQ Dw l) → Matrix (Fin S.rank) (Fin T.rank) D.host.E}
    (hY₀ : IsRoots l (latG T 1) ι l.M Y₀) (hY : IsRoots l (latG T g) mk N Y) {q : Fin S.rank → LevQ Dw l}
    (hq : ∀ b, (B : 𝓞 D.host.E) • q b = 0) :
    heisO C.ψ S T (actO S T h g (finW S T (Y₀ q))) f = heisO C.ψ S T (finW S T (Y q)) f := by
  have hV := Base.stdL_mem_Vset (E := D.host.E) S.rank 1
  have m1 : ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T g)), actO S T h 1 u ∈ hatA S T (tens Λ (latG T g)) :=
    fun u hu => (mem_hatA_iff S T C.m.gS h 1 _ _ _ _ hmv (isMov_fmt_one _) _).2 ⟨u, hu, rfl⟩
  have m2 : ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T 1)), actO S T h g u ∈ hatA S T (tens Λ (latG T g)) :=
    fun u hu => (mem_hatA_iff S T C.m.gS h g _ _ _ _ hmv (isMov_latG g) _).2 ⟨u, hu, rfl⟩
  choose a ha ea ya using fun b => (hY q b).1
  choose a₀ ha₀ ea₀ ya₀ using fun b => (hY₀ q b).1
  have f1 : actO S T 1 g (finW S T (Y₀ q)) - finW S T (Y q) ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T g)) := by
    rw [finW_eq_colM, finW_eq_colM, actO_colM, ← map_sub]
    exact colM_mem fun b => root_cong hι hm (ha b) (ha₀ b) ((ea₀ b).trans (ea b).symm) (ya b) (ya₀ b)
  have f2 : ∀ n : ℕ, (∀ b, (n : 𝓞 D.host.E) • q b = 0) →
      n • finW S T (Y q) ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T g)) := fun n hn => by
    rw [← finW_nsmul]
    exact finW_mem fun b => nsmul_root_mem hmk (ha b) (ya b) (by rw [ea b]; exact hn b)
  have hMb : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
    have hMM : (l.M : 𝓞 D.host.E) ∈ l.Mb * Mfr l := l.prod.ge (Ideal.subset_span rfl)
    exact Ideal.mul_le_left hMM
  have f3 := f2 l.M fun b => by
    rw [← ea b, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hMb trivial
  have f4 : (e + cA D e) • finW S T (Y q) ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T g)) := by
    have hB0 : (B : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hB
    have hB1 : (B : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hB
    have i1 : finPart D (e * incA D (B : D.host.E)⁻¹) ∈ Formalism.L2.Theta.intAE D := by
      obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
      rw [Finset.sum_mul, map_sum]
      refine sum_mem fun PP hPP => ?_
      by_contra hn
      exact hP PP hPP (((hes PP hPP).2 _ hB0).2 hn)
    have i2 : incA D (B : D.host.E)⁻¹ * (B : Formalism.L2.Theta.AE D) = 1 := by
      rw [← map_natCast (incA D), ← RingHom.map_mul, inv_mul_cancel₀ hB1, RingHom.map_one]
    have i3 : cA D (incA D (B : D.host.E)⁻¹) * (B : Formalism.L2.Theta.AE D) = 1 := by
      rw [← map_natCast (cA D), ← RingHom.map_mul, i2, RingHom.map_one]
    obtain ⟨j1, j2⟩ := smul_mem_of_int hV i1 (f2 B hq)
    rw [← Nat.cast_smul_eq_nsmul (Formalism.L2.Theta.AE D), smul_smul] at j1 j2
    rw [mul_assoc, i2, mul_one] at j1
    rw [RingHom.map_mul, mul_assoc, i3, mul_one] at j2
    rw [add_smul]
    exact add_mem j1 j2
  have f5 : k • (actO S T h g (finW S T (Y₀ q)) - finW S T (Y q)) ∈ hatA S T (tens Λ (latG T g)) := by
    have := add_mem (nsmul_mem (m1 _ f1) k) (sub_mem (nsmul_mem (m1 _ f4) k) (nsmul_mem_of_le hk' f4))
    rwa [← nsmul_sub, ← actO_sub_self hs, LevEig.actO_sub, ← actO_split, ← nsmul_add, sub_add_sub_cancel] at this
  obtain ⟨j, hj⟩ := exists_pow fun b => (hY q b).2
  obtain ⟨j₀, hj₀⟩ := exists_pow fun b => (hY₀ q b).2
  obtain ⟨s, hs, t, ht, est⟩ := exists_split l hk (max j j₀)
  have g1 : ∀ s ∈ l.Mb ^ max j j₀, ∃ u ∈ hatA S T (tens Λ (latG T g)),
      incA D (s : D.host.E) • actO S T h g (finW S T (Y₀ q)) = (2 * l.M) • u := fun s hs => by
    obtain ⟨u, hu, eu⟩ := hj₀ _ (le_max_right _ _) s hs
    refine ⟨_, m2 _ (finW_mem hu), ?_⟩
    rw [← actO_smul, inc_smul_finW, eu, finW_nsmul]
    exact map_nsmul (TensLatMove.actHom S T h g) _ _
  have g2 : ∀ s ∈ l.Mb ^ max j j₀, ∃ u ∈ hatA S T (tens (stdL D.host.E S.rank) (latG T g)),
      incA D (s : D.host.E) • finW S T (Y q) = (2 * N) • u := fun s hs => by
    obtain ⟨u, hu, eu⟩ := hj _ (le_max_left _ _) s hs
    exact ⟨_, finW_mem hu, by rw [inc_smul_finW, eu, finW_nsmul]⟩
  have hbar : cA D (incA D (t : D.host.E)) = incA D (H.bar t : D.host.E) := by rw [H.bar_eq]; rfl
  refine heis_congr (σ := incA D (s : D.host.E)) (τ := incA D (t : D.host.E)) (k := k) (M := l.M)
    (char_hatA C hΛ hL) hf ?_ (fun u hu => (smul_mem_of_int hΛ ?_ hu).1) f5 (nsmul_mem_of_le hk' f3) ?_ ?_ ?_ ?_
  · have := congrArg ((incA D).comp (algebraMap (𝓞 D.host.E) D.host.E)) est
    rwa [RingHom.map_add, RingHom.map_mul, map_natCast, RingHom.map_one] at this
  · exact AddSubgroup.subset_closure ⟨1, intAf_one, t, rfl⟩
  · obtain ⟨u, hu, eu⟩ := g1 s hs
    exact ⟨_, nsmul_mem hu l.M, by rw [eu, mul_nsmul']⟩
  · obtain ⟨u, hu, eu⟩ := g2 s hs
    exact ⟨_, nsmul_mem_of_le hN' hu, by rw [eu, mul_nsmul']⟩
  · rw [hbar]
    exact g1 _ ht
  · obtain ⟨u, hu, eu⟩ := g2 _ ht
    obtain ⟨c, rfl⟩ := hN
    refine ⟨_, nsmul_mem (nsmul_mem_of_le hk' hu) c, ?_⟩
    rw [hbar, eu, ← mul_nsmul', ← mul_nsmul', ← mul_nsmul']
    congr 1
    ring

theorem isRoots_neg {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {n r N : ℕ}
    {L : Lt D.host.E r} {mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)}
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) D.host.E} (hY : IsRoots l L mk N Y) :
    IsRoots l L (-mk) N fun q => -Y q := by
  intro q b
  obtain ⟨⟨a, ha, ea, ya⟩, j, hj⟩ := hY q b
  refine ⟨⟨a, ha, ea, ?_⟩, j, fun s hs => ?_⟩
  · have := neg_mem ya
    rw [neg_sub'] at this
    rwa [LinearMap.neg_apply, smul_neg]
  · obtain ⟨u, hu, e⟩ := hj s hs
    exact ⟨-u, neg_mem hu, by rw [smul_neg, ← e, ← smul_neg]; rfl⟩

theorem markAd_zsmul {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {g : GA D T}
    {ι mk : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)} (hm : MarkAd (T := T) rfl l ι g mk) (ε : ℤ) :
    MarkAd (T := T) rfl l (-(ε • ι)) g (-(ε • mk)) := by
  intro a ha
  have e (f : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)) : (-(ε • f)) a = f (-(ε • a)) := by simp
  rw [e, e]
  exact hm _ (neg_mem (zsmul_mem ha ε))

theorem heis_root_zak {r g : ℕ} (hr : T.rank = r) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {X : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    (hS : IsSet ψ θ S T hr X eT bas) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeak ψ S T om)
    {w : D.host.E} (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) (hw2 : IdemTwo w) {Z : Fam T} (hZ : IsONeg T X.p0 Z)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {h : GA D S} {g' : GA D T} {Λ : Lt D.host.E S.rank} (hΛ : Λ ∈ Vset D.host.E S.rank 1)
    (hmv : IsMov (fmtC S h) (stdL D.host.E S.rank) Λ) {L : Lt D.host.E r} (hL : SelfD X L) (hLG : latW hr L = latG T g')
    {v : TF S.rank g} (hv : IsVac X bas w (tens (stdL D.host.E S.rank) L) v) {a : ℂ} {f : WO S T → ℂ}
    (hf : Zak ψ θ hr eT bas idx (frOf hr eT Z) (a • v) f) {ι mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)}
    (hι : LatEmb T (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι)) (hmk : ∀ a, mk a ∈ L)
    (hm : MarkAd hr l (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι) g' mk) {N k B : ℕ} (hN : l.M ∣ N)
    (hN' : Ideal.span {(N : 𝓞 D.host.E)} • stdL D.host.E S.rank ≤ Λ) (hk : Nat.Coprime k l.M)
    (hk' : Ideal.span {(k : 𝓞 D.host.E)} • stdL D.host.E S.rank ≤ Λ) (hB : B ≠ 0) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (hP : ∀ PP ∈ P, (B : 𝓞 D.host.E) ∉ PP.asIdeal) (hs : SuppAt e S h)
    {ε : ℤ} {Y₀ Y : (Fin S.rank → LevQ Dw l) → Matrix (Fin S.rank) (Fin r) D.host.E}
    (hY₀ : IsRoots l (LinearMap.range ι) (ε • ι) l.M Y₀) (hY : IsRoots l L (ε • mk) N Y) {q : Fin S.rank → LevQ Dw l}
    (hq : ∀ b, (B : 𝓞 D.host.E) • q b = 0) :
    heisO ψ S T (actO S T h g' (finR S hr (-Y₀ q))) (om (h, 1) f) = heisO ψ S T (finR S hr (-Y q)) (om (h, 1) f) := by
  subst hr
  obtain rfl : L = latG T g' := hLG
  replace hm : MarkAd (T := T) rfl l ι g' mk := hm
  have hι' : LinearMap.range ι = latG T 1 := hι.2
  rw [hι'] at hY₀
  obtain ⟨X', m, hq', bas', idx', hsy, π, -, hEF, -⟩ := Flip.exists_flip_model D S T _ g rfl ψ θ X eT bas idx hS
    (T.rank - X.p0) (Nat.add_sub_cancel' X.p0_le)
  replace hEF : ∀ u v, EF X' u v = EF X u v := hEF
  have hL' : SelfD X' (latG T g') := ⟨hL.1, by simpa only [hEF] using hL.2⟩
  let C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hsy
  have hz := (GlobalTheory.T.adelicTheta_of_testFunction_exists_laws_fockVectors D S T _ g rfl ψ θ X eT bas idx hS Z hZ).1
  have hsb := Const.isSB_smul_tf a hv.1
  have hlat : IsLatVac (heisO ψ S T) (hatA S T (tens (stdL D.host.E S.rank) (latG T g'))) f := by
    refine (SignVac.isLatVac_iff D S T C w hw hw' hw2 1 _ (Base.stdL_mem_Vset _ 1) _ hL' f hf.1).2 fun y hy => ?_
    obtain ⟨u1, -, -, -, u5, -⟩ := (hz _ hsb).2 f hf
    have hsb' := ((heisG_laws _ _ X g bas idx S.rank hS.2.2.2.2.2.2.2 hS.2.2.2.1).2.2.2 (-y) _ hsb).1
    have h1 := ((hz _ hsb').2 _ (u5 y)).2.2.1 (SW.epsW X w (-y))
    have h2 : SW.epsW X w (-y) • heisG X bas (-y) (a • v) = a • v := by
      rw [heisG_smul, smul_comm, hv.2.2 _ (neg_mem hy)]
    have h3 : SW.epsW C.X w y = SW.epsW X w (-y) := by
      rw [epsW_neg_rows]
      change SW.epsW X' w y = _
      simp only [SW.epsW, hEF]
    rw [h2] at h1
    rw [h3]
    exact u1 _ h1
  have hlat' := (hatA_move D S T C h 1 _ _ _ _ hmv (isMov_fmt_one _)).2 om hom f hf.1 hlat
  exact heis_root C hΛ hmv hL' hlat'.1 (fun a => neg_mem (zsmul_mem (hι' ▸ LinearMap.mem_range_self ι a) ε))
    (fun a => neg_mem (zsmul_mem (hmk a) ε)) (markAd_zsmul hm ε) hN hN' hk hk' hB he hP hs (isRoots_neg hY₀)
    (isRoots_neg hY) hq

theorem zak_sum {r g : ℕ} {hr : T.rank = r} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {X : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    (hS : IsSet ψ θ S T hr X eT bas) {Z : Fam T} (hZ : IsONeg T X.p0 Z) {φ : TF S.rank g} (hφ : SW.IsSB φ)
    {f : WO S T → ℂ} (hf : Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f) {Q : Type} [Fintype Q] (W : Q → ℂ)
    (Y : Q → Matrix (Fin S.rank) (Fin r) D.host.E) (c : ℂ) :
    Zak ψ θ hr eT bas idx (frOf hr eT Z) (c • ∑ q, W q • heisG X bas (Y q) φ)
      (c • ∑ q, W q • heisO ψ S T (finR S hr (-Y q)) f) := by
  classical
  have hz := (GlobalTheory.T.adelicTheta_of_testFunction_exists_laws_fockVectors D S T _ g hr ψ θ X eT bas idx hS Z hZ).1
  have key : ∀ s : Finset Q, SW.IsSB (∑ q ∈ s, W q • heisG X bas (Y q) φ) ∧ Zak ψ θ hr eT bas idx (frOf hr eT Z)
      (∑ q ∈ s, W q • heisG X bas (Y q) φ) (∑ q ∈ s, W q • heisO ψ S T (finR S hr (-Y q)) f) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have := ((hz φ hφ).2 f hf).2.2.1 0
      rw [zero_smul, zero_smul] at this
      exact ⟨isSB_zero, this⟩
    | insert q s hq ih =>
      rw [Finset.sum_insert hq, Finset.sum_insert hq]
      have h1 := ((heisG_laws _ _ X g bas idx S.rank hS.2.2.2.2.2.2.2 hS.2.2.2.1).2.2.2 (Y q) _ hφ).1
      have h2 := ((hz φ hφ).2 f hf).2.2.2.2.1 (-Y q)
      rw [neg_neg] at h2
      have h3 := Const.isSB_smul_tf (W q) h1
      exact ⟨(isSB_algebra_haar_linear ℚ _ _ _ _ h3 ih.1).1,
        ((hz _ h3).2 _ (((hz _ h1).2 _ h2).2.2.1 (W q))).2.2.2.1 _ _ ih.1 ih.2⟩
  exact ((hz _ (key _).1).2 _ (key _).2).2.2.1 c

end GlobalTheory.OneMapRef.Term
