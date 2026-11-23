import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoFinitePlaceTruncationAdeleE
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceWeilRepLatticeVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameCharacterFromProduct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts
open GlobalTheory.VecInv GlobalTheory.GeoActCompare.TameConj

namespace GlobalTheory.FinVac

section Generic

theorem units_tendsto {M ι : Type} [Monoid M] [TopologicalSpace M] {l : Filter ι} {f : ι → Mˣ} {u : Mˣ}
    (h1 : Filter.Tendsto (fun i => (f i : M)) l (nhds (u : M)))
    (h2 : Filter.Tendsto (fun i => (((f i)⁻¹ : Mˣ) : M)) l (nhds ((u⁻¹ : Mˣ) : M))) :
    Filter.Tendsto f l (nhds u) := by
  rw [Units.isEmbedding_embedProduct.isInducing.tendsto_nhds_iff]
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def cut (a : A) (ha : a * a = a) : Aˣ →* Aˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => a * (x : A) + (1 - a)
      map_one' := by rw [Units.val_one]; ring
      map_mul' := fun x y => by
        rw [Units.val_mul]
        linear_combination (-(x : A) * (y : A) + x + y - 1) * ha }

theorem cut_val (a : A) (ha : a * a = a) (x : Aˣ) : ((cut a ha x : Aˣ) : A) = a * (x : A) + (1 - a) := rfl

theorem cut_add {a b : A} (ha : a * a = a) (hb : b * b = b) (hc : (a + b) * (a + b) = a + b) (hab : a * b = 0)
    (x : Aˣ) : cut (a + b) hc x = cut a ha x * cut b hb x := by
  refine Units.ext ?_
  rw [Units.val_mul, cut_val, cut_val, cut_val]
  linear_combination (-(x : A) * x + 2 * x - 1) * hab

theorem cut_mul {a b : A} (hab : a * b = 0) (m : Matrix n n A) :
    (a + b) • m + (1 - (a + b)) • (1 : Matrix n n A) =
      (a • m + (1 - a) • (1 : Matrix n n A)) * (b • m + (1 - b) • (1 : Matrix n n A)) := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, hab, zero_smul, zero_add]
  have h1 : a * (1 - b) = a := by linear_combination -hab
  have h2 : (1 - a) * b = b := by linear_combination -hab
  have h3 : (1 - a) * (1 - b) = 1 - (a + b) := by linear_combination hab
  rw [h1, h2, h3, add_smul]
  abel

omit [Fintype n] in
theorem cut_entry (a : A) (m : Matrix n n A) (i j : n) :
    (a • m + (1 - a) • (1 : Matrix n n A)) i j = a * (m - 1) i j + (1 : Matrix n n A) i j := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

omit [Fintype n] in
theorem cut_supp {a : A} (ha : a * a = a) (m : Matrix n n A) (i j : n) :
    a * (a • m + (1 - a) • (1 : Matrix n n A) - 1) i j = (a • m + (1 - a) • (1 : Matrix n n A) - 1) i j := by
  rw [Matrix.sub_apply, cut_entry]
  linear_combination (m - 1) i j * ha

theorem mul_det_congr (b : A) (M N : Matrix n n A) (h : ∀ i j, b * (M i j - N i j) = 0) :
    b * (M.det - N.det) = 0 := by
  let I : Ideal A := LinearMap.ker (LinearMap.mulLeft A b)
  have hI : ∀ x, x ∈ I ↔ b * x = 0 := fun x => Iff.rfl
  rw [← hI, ← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  exact Ideal.Quotient.eq.2 ((hI _).2 (h i j))

theorem mul_det_cut {a : A} (ha : a * a = a) (m M : Matrix n n A) (hM : M = a • m + (1 - a) • (1 : Matrix n n A)) :
    a * M.det = a * m.det := by
  rw [hM, ← sub_eq_zero, ← mul_sub]
  refine mul_det_congr a _ _ fun i j => ?_
  rw [cut_entry, Matrix.sub_apply]
  linear_combination (m i j - (1 : Matrix n n A) i j) * ha

theorem cmRing_idempotent_unitRatio_identity {e c d d' x y : A} (he : e * e = e) (hc : c * c = c) (hec : e * c = 0)
    (hd : (e + c) * d' = (e + c) * d) (hx : x = d * y) :
    (e + c) * x + (1 - (e + c)) = (e * d' + (1 - e)) * ((e * y + (1 - e)) * (c * x + (1 - c))) := by
  have h1 : e * d' = e * d := by linear_combination e * hd + (d - d') * he + (d - d') * hec
  rw [h1]
  linear_combination e * hx + (1 - y) * (d - 1) * he - (e * d + 1 - e) * ((y - 1) * (x - 1)) * hec
    - (d - 1) * (x - 1) * hec

theorem cut_root (c : A →+* A) (hcc : ∀ z, c (c z) = z) {e d d' : A} (he : e * e = e) (hc : c e * c e = c e)
    (hec : e * c e = 0) (hb : (e + c e) * (e + c e) = e + c e) (x u : Aˣ) (hu : (u : A) = e * d' + (1 - e))
    (hd : (e + c e) * d' = (e + c e) * d) (hx : (x : A) = d * c x) :
    cut (e + c e) hb x = u * (cut e he (Units.map c.toMonoidHom x) * cut (c e) hc x) ∧
      c ((cut e he (Units.map c.toMonoidHom x) * cut (c e) hc x : Aˣ) : A) =
        ((cut e he (Units.map c.toMonoidHom x) * cut (c e) hc x : Aˣ) : A) := by
  have hv : ((cut e he (Units.map c.toMonoidHom x) * cut (c e) hc x : Aˣ) : A) =
      (e * c (x : A) + (1 - e)) * (c e * (x : A) + (1 - c e)) := rfl
  refine ⟨Units.ext ?_, ?_⟩
  · rw [Units.val_mul, hv, cut_val, hu]
    exact cmRing_idempotent_unitRatio_identity he hc hec hd hx
  · rw [hv]
    simp only [map_mul, map_add, map_sub, map_one, hcc]
    exact mul_comm _ _

theorem eig_limit {G H U W ι : Type} [Group G] [Group H] [Monoid U] [TopologicalSpace G] [TopologicalSpace H]
    [TopologicalSpace U] (om : G × H →* Module.End ℂ (W → ℂ)) (χ χ' : U →* Circle) {f : W → ℂ}
    (hom : ∀ w, Continuous fun p => om p f w) (hχ : Continuous χ) (hχ' : Continuous χ') {l : Filter ι} [l.NeBot]
    {g : ι → G} {h : ι → H} {x y : ι → U} {g₀ : G} {h₀ : H} {x₀ y₀ : U} (tg : Filter.Tendsto g l (nhds g₀))
    (th : Filter.Tendsto h l (nhds h₀)) (tx : Filter.Tendsto x l (nhds x₀)) (ty : Filter.Tendsto y l (nhds y₀))
    (he : ∀ s, om (g s, h s) f = ((((χ (x s))⁻¹ * χ' (y s) : Circle)) : ℂ) • f) :
    om (g₀, h₀) f = ((((χ x₀)⁻¹ * χ' y₀ : Circle)) : ℂ) • f := by
  funext w
  have t1 := ((hom w).tendsto (g₀, h₀)).comp (tg.prodMk_nhds th)
  have t2 := ((continuous_subtype_val.tendsto _).comp
    ((((hχ.tendsto x₀).comp tx).inv).mul ((hχ'.tendsto y₀).comp ty))).mul_const (f w)
  exact tendsto_nhds_unique t1 (t2.congr fun s => (congrFun (he s) w).symm)

theorem sum_idem {ι : Type} (p : ι → A) (s : Finset ι) (h : ∀ i, p i * p i = p i)
    (h0 : ∀ i j, i ≠ j → p i * p j = 0) : (∑ i ∈ s, p i) * (∑ i ∈ s, p i) = ∑ i ∈ s, p i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => h0 i j hji.symm) (fun h => absurd hi h), h i]

theorem eig_mul {G H U M : Type} [Group G] [Group H] [Monoid U] [AddCommGroup M] [Module ℂ M]
    (om : G × H →* Module.End ℂ M) (χ χ' : U →* Circle) {f : M} {g g' : G} {h h' : H} {x x' y y' : U}
    (h1 : om (g, h) f = ((((χ x)⁻¹ * χ' y : Circle)) : ℂ) • f)
    (h2 : om (g', h') f = ((((χ x')⁻¹ * χ' y' : Circle)) : ℂ) • f) :
    ∀ {g₁ h₁ x₁ y₁}, g₁ = g * g' → h₁ = h * h' → x₁ = x * x' → y₁ = y * y' →
      om (g₁, h₁) f = ((((χ x₁)⁻¹ * χ' y₁ : Circle)) : ℂ) • f := by
  rintro _ _ _ _ rfl rfl rfl rfl
  rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, h2, map_smul, h1, smul_smul, ← Circle.coe_mul, map_mul,
    map_mul, mul_inv, mul_mul_mul_comm, mul_comm (χ x)⁻¹, mul_comm (χ' y)]

theorem eig_one {G H U M : Type} [Group G] [Group H] [Monoid U] [AddCommGroup M] [Module ℂ M]
    (om : G × H →* Module.End ℂ M) (χ χ' : U →* Circle) (f : M) :
    ∀ {g₁ h₁ x₁ y₁}, g₁ = 1 → h₁ = 1 → x₁ = 1 → y₁ = 1 →
      om (g₁, h₁) f = ((((χ x₁)⁻¹ * χ' y₁ : Circle)) : ℂ) • f := by
  rintro _ _ _ _ rfl rfl rfl rfl
  rw [map_one, map_one, inv_one, mul_one, Circle.coe_one, one_smul, Prod.mk_one_one, map_one, Module.End.one_apply]

end Generic

variable {D : D7}

theorem exists_placeIdem (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ ε, IsPlaceIdem D v ε := by
  classical
  exact ⟨_, singleV D.host.F v 1, rfl,
    Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) v 1,
    fun w hw => Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) hw 1⟩

theorem placeIdem_idem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  refine Prod.ext (mul_zero _) ?_
  change α * α = α
  refine RestrictedProduct.ext _ _ fun w => ?_
  change evalV D.host.F w (α * α) = evalV D.host.F w α
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [h1, mul_one]
  · rw [h0 w hw, zero_mul]

theorem finUnit_cut {a : AE D} (ha : a * a = a) {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit (cut a ha x) := by
  have h2 : finPart D a ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])
  have h3 : finPart D (1 - a) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul]; congr 1; linear_combination ha)
  have key : ∀ y : (AE D)ˣ, finPart D (y : AE D) ∈ intAE D → finPart D ((cut a ha y : (AE D)ˣ) : AE D) ∈ intAE D :=
    fun y hy => by
      rw [cut_val, RingHom.map_add, RingHom.map_mul]
      exact add_mem (mul_mem_intAE h2 hy) h3
  refine ⟨?_, key x hx.2.1, ?_⟩
  · rw [cut_val, RingHom.map_add, RingHom.map_mul, hx.1, mul_one, ← RingHom.map_add, add_sub_cancel,
      RingHom.map_one]
  · rw [← MonoidHom.map_inv]
    exact key _ hx.2.2

theorem char_fixed (V : HSp D) (hη : ∃ η, IsEtaTilde D η) {χ : (AE D)ˣ →* Circle} {n : ℕ} (hχ : ResEta D χ n)
    {z : (AE D)ˣ} (hz : FinUnit z) (hc : cA D (z : AE D) = z) : χ z = 1 := by
  obtain ⟨η, -, h1, h2, -⟩ := hη
  obtain ⟨η₀, h0⟩ := hχ.1
  have r : ∀ w : (AE D)ˣ, cA D (w : AE D) = w → IsDetRoot V 1 w := fun w hw => by
    change (w : AE D) = (Formalism.L2.Theta.mt V 1).det * cA D (w : AE D)
    rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one, one_mul, hw]
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 1 1 z (r 1 (RingHom.map_one _)) (r z hc)
  rw [one_mul] at ha
  have h3 := h1 z hz.1 hz.2.1 hz.2.2
  rw [ha, h2.2 η₀ h0, pow_one] at h3
  rw [ha, hχ.2 η₀ h0, h3, one_pow]

theorem exists_detAt (V : HSp D) (hη : ∃ η, IsEtaTilde D η) {χ : (AE D)ˣ →* Circle} {n : ℕ} (hχ : ResEta D χ n)
    {e b : AE D} (he : IsSplitIdem D e) (hb : b * b = b) (heb : e + cA D e = b) {k k₁ : GA D V} {x : (AE D)ˣ}
    (hx : FinUnit x) (hr : IsDetRoot V k x)
    (hk : Formalism.L2.Theta.mt V k₁ = b • Formalism.L2.Theta.mt V k + (1 - b) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) :
    ∃ u, IsDetAt e V k₁ u ∧ χ u = χ (cut b hb x) := by
  subst heb
  have hc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he.1]
  have hz : FinUnit (cut e he.1 (Units.map (cA D).toMonoidHom x) * cut (cA D e) hc x) :=
    FinUnit_mul (finUnit_cut _ (FinUnit_conj hx)) (finUnit_cut _ hx)
  obtain ⟨h2, h3⟩ := cut_root (cA D) Formalism.L2.Theta.cA_cA he.1 hc he.2.1 hb x (detAt e he.1 V k₁)
    (isDetAt_detAt e he.1 V k₁) (mul_det_cut hb (Formalism.L2.Theta.mt V k) (Formalism.L2.Theta.mt V k₁) hk) hr
  refine ⟨detAt e he.1 V k₁, isDetAt_detAt _ _ _ _, ?_⟩
  rw [h2, MonoidHom.map_mul, char_fixed V hη hχ hz h3, mul_one]

theorem stab_of_isMov (V : HSp D) {Λ : Lt D.host.E V.rank} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {k : GA D V} (hk : k ∈ GfC V) (h : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt V k) Λ Λ) :
    Stab V β k := by
  refine ⟨hk, (GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).2 ?_⟩
  refine (GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2
    (Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)))
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) (GlobalTheory.LevSplit.latHat_iff Λ) (finHom V k)).1 fun y => ?_
  refine ⟨fun hy => (h _).2 ⟨y, hy, rfl⟩, fun hy => ?_⟩
  obtain ⟨u, hu, e⟩ := (h _).1 hy
  have e' : (finHom V k).1 *ᵥ y = (finHom V k).1 *ᵥ u := e
  have := congrArg (fun w => ((finHom V k)⁻¹).1 *ᵥ w) e'
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
  rw [this]
  exact hu

theorem infPart_entry (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  have h : infHom V g = 1 := hg
  have h2 : infPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun u : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.val i j) h
  rw [Matrix.sub_apply, RingHom.map_sub, h2, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one, sub_self]
  · rw [RingHom.map_zero, sub_self]

section Trunc

variable {ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F} (hε : ∀ v, IsPlaceIdem D v (ε v))

def idS (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F) (s : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AE D :=
  algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v)

include hε

theorem sum_place_idem (s : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    (∑ v ∈ s, ε v) * (∑ v ∈ s, ε v) = ∑ v ∈ s, ε v :=
  sum_idem ε s (fun v => placeIdem_idem (hε v)) fun v w h => GlobalTheory.PlaceDatum.placeIdem_mul (hε v) (hε w) h

theorem idS_idem (s : Finset (HeightOneSpectrum (𝓞 D.host.F))) : idS ε s * idS ε s = idS ε s := by
  unfold idS
  rw [← RingHom.map_mul, sum_place_idem hε]

omit hε in
theorem idS_cons {v} {s : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hv : v ∉ s) :
    idS ε (Finset.cons v s hv) = idS ε {v} + idS ε s := by
  unfold idS
  rw [Finset.sum_cons, Finset.sum_singleton, RingHom.map_add]

theorem idS_orth {v} {s : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hv : v ∉ s) : idS ε {v} * idS ε s = 0 := by
  unfold idS
  rw [← RingHom.map_mul, Finset.sum_singleton, Finset.mul_sum, Finset.sum_eq_zero, RingHom.map_zero]
  exact fun w hw => GlobalTheory.PlaceDatum.placeIdem_mul (hε v) (hε w) fun e => hv (e ▸ hw)

theorem cut_empty (z : (AE D)ˣ) : cut _ (idS_idem hε ∅) z = 1 := Units.ext (by
  rw [cut_val, idS, Finset.sum_empty, RingHom.map_zero, zero_mul, zero_add, sub_zero, Units.val_one])

theorem cut_cons {v} {s : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hv : v ∉ s) (z : (AE D)ˣ) :
    cut _ (idS_idem hε (Finset.cons v s hv)) z = cut _ (idS_idem hε {v}) z * cut _ (idS_idem hε s) z := by
  rw [← cut_add _ _ (idS_cons hv ▸ idS_idem hε (Finset.cons v s hv)) (idS_orth hε hv)]
  refine Units.ext ?_
  rw [cut_val, cut_val, idS_cons]

theorem tendsto_cut {x : (AE D)ˣ} (hx : FinUnit x) :
    Filter.Tendsto (fun s => cut (idS ε s) (idS_idem hε s) x) Filter.atTop (nhds x) := by
  have : ContinuousAdd (AE D) := ModuleTopology.continuousAdd (AF D.host.F) (AE D)
  have key : ∀ y : (AE D)ˣ, FinUnit y → Filter.Tendsto
      (fun s => ((cut (idS ε s) (idS_idem hε s) y : (AE D)ˣ) : AE D)) Filter.atTop (nhds (y : AE D)) := fun y hy => by
    have h := (GlobalTheory.VecInv.tendsto_truncation D ε hε ((y : AE D) - 1)
      (by rw [RingHom.map_sub, hy.1, RingHom.map_one, sub_self])).add_const 1
    rw [sub_add_cancel] at h
    refine h.congr fun s => ?_
    rw [cut_val, idS]
    ring
  refine units_tendsto (key x hx) ((key _ (FinUnit_inv hx)).congr fun s => ?_)
  rw [MonoidHom.map_inv]

theorem exists_trunc (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    ∃ κ : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V → GA D V,
      (∀ g, κ ∅ g = 1) ∧
      (∀ v s (hv : v ∉ s) g, κ (Finset.cons v s hv) g = κ {v} g * κ s g) ∧
      (∀ v g, Stab V β g → Stab V β (κ {v} g) ∧ SuppPl (ε v) V (κ {v} g) ∧ Formalism.L2.Theta.mt V (κ {v} g) =
        idS ε {v} • Formalism.L2.Theta.mt V g + (1 - idS ε {v}) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      ∀ g, Stab V β g → Filter.Tendsto (fun s => κ s g) Filter.atTop (nhds g) := by
  choose κ hκ using fun s => GlobalTheory.UnitaryIdemCut.exists_cut D V β _ (sum_place_idem hε s)
  have inj : ∀ {g h : GA D V}, Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V h → g = h := fun e => Subtype.ext (Units.ext e)
  have lim : ∀ g, Stab V β g → Filter.Tendsto (fun s => Formalism.L2.Theta.mt V (κ s g)) Filter.atTop
      (nhds (Formalism.L2.Theta.mt V g)) := fun g hg => by
    have : ContinuousAdd (AE D) := ModuleTopology.continuousAdd (AF D.host.F) (AE D)
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have h := (GlobalTheory.VecInv.tendsto_truncation D ε hε _ (infPart_entry V hg.1 i j)).add_const
      ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
    rw [Matrix.sub_apply, sub_add_cancel] at h
    refine h.congr fun s => ?_
    rw [(hκ s g).1, cut_entry, Matrix.sub_apply]
  refine ⟨fun s g => κ s g, fun g => inj ?_, fun v s hv g => inj ?_,
    fun v g hg => ⟨(hκ _ g).2 hg, ?_, (hκ _ g).1⟩,
    fun g hg => tendsto_subtype_rng.2 (units_tendsto (lim g hg) ?_)⟩
  · rw [(hκ _ g).1, Finset.sum_empty, RingHom.map_zero, zero_smul, sub_zero, one_smul, zero_add,
      GlobalTheory.AdelicLatMove.mt_one]
  · rw [GlobalTheory.AdelicLatMove.mt_mul, (hκ _ g).1, (hκ _ g).1, (hκ _ g).1]
    change idS ε _ • _ + (1 - idS ε _) • _ = _
    rw [idS_cons]
    exact cut_mul (idS_orth hε hv) _
  · intro i j
    rw [(hκ _ g).1, Finset.sum_singleton]
    refine cut_supp ?_ _ i j
    rw [← RingHom.map_mul, placeIdem_idem (hε v)]
  · refine (lim g⁻¹ hg.inv).congr fun s => ?_
    rw [MonoidHom.map_inv]
    rfl

end Trunc

theorem unram_cut {ε : AF D.host.F} {χ : (AE D)ˣ →* Circle} (hχ : UnramAt ε χ) {b : AE D} (hb : b * b = b)
    (e : b = algebraMap (AF D.host.F) (AE D) ε) {x : (AE D)ˣ} (hx : FinUnit x) : χ (cut b hb x) = 1 := by
  refine hχ _ ?_ (finUnit_cut hb hx).2.1 (finUnit_cut hb hx).2.2
  rw [cut_val, ← e]
  linear_combination ((x : AE D) - 1) * hb

theorem om_vacuum_finite : ∀ (D : D7) (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → S.SigOK → T.SigOK → ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∃ η, IsEtaTilde D η) → (∀ v ε, NonSplitAt D v ε → UnramAt ε χS ∧ UnramAt ε χT) → ∀ (sS : Fam S) (sT : Fam T), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Lt D.host.E S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt S k) ΛS ΛS → GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T k') ΛT ΛT → ∀ x y : (AE D)ˣ, FinUnit x → FinUnit y → IsDetRoot S k x → IsDetRoot T k' y → om (k, k') f = ((((χT x)⁻¹ * χS y : Circle)) : ℂ) • f := by
  intro D S T ψ θ _ _ _ χS χT om hW hη hun sS sT _ _ ΛS ΛT hS hT f hf k hk k' hk' mk mk' x y hx hy rx ry
  obtain ⟨βS, hβS⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E _ ΛS hS.1
  obtain ⟨βT, hβT⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E _ ΛT hT.1
  have hg := stab_of_isMov S hβS hk mk
  have hh := stab_of_isMov T hβT hk' mk'
  have hth := hf.2.theta
  have hvac := hf.2.lat
  choose ε hε using exists_placeIdem (D := D)
  obtain ⟨κ, a0, a1, a2, a3⟩ := exists_trunc hε S βS
  obtain ⟨μ, b0, b1, b2, b3⟩ := exists_trunc hε T βT
  have hloc : ∀ v, om (κ {v} k, μ {v} k') f = ((((χT (cut _ (idS_idem hε {v}) x))⁻¹ *
      χS (cut _ (idS_idem hε {v}) y) : Circle)) : ℂ) • f := by
    intro v
    obtain ⟨p1, p2, p3⟩ := a2 v k hg
    obtain ⟨q1, q2, q3⟩ := b2 v k' hh
    have hlat := mem_latO_iff hβS hβT p1.2 q1.2
    have hv : idS ε {v} = algebraMap (AF D.host.F) (AE D) (ε v) := by rw [idS, Finset.sum_singleton]
    by_cases hsp : ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) (ε v)
    · obtain ⟨e, he, hb⟩ := hsp
      obtain ⟨u, hu, eu⟩ := exists_detAt S hη hW.resT he (idS_idem hε {v}) (hb.trans hv.symm) hx rx p3
      obtain ⟨w, hw, ew⟩ := exists_detAt T hη hW.resS he (idS_idem hε {v}) (hb.trans hv.symm) hy ry q3
      rw [← eu, ← ew]
      exact om_latVac_split D ψ S T ΛS ΛT χS χT om hW hS hT e he _ _
        (fun i j => by rw [hb]; exact p2 i j) (fun i j => by rw [hb]; exact q2 i j) hlat u w hu hw f hth hvac
    · obtain ⟨uS, uT⟩ := hun v _ ⟨hε v, hsp⟩
      rw [unram_cut uT _ hv hx, unram_cut uS _ hv hy, inv_one, mul_one, Circle.coe_one, one_smul]
      exact GlobalTheory.T.weilOperator_lattice_stabiliser_fixes_vacuum_nonsplit D ψ S T ΛS ΛT χS χT om hW hS hT hη v _ ⟨hε v, hsp⟩ uS uT _ _ p2 q2 hlat f hth hvac
  have hfin : ∀ s, om (κ s k, μ s k') f = ((((χT (cut _ (idS_idem hε s) x))⁻¹ *
      χS (cut _ (idS_idem hε s) y) : Circle)) : ℂ) • f := by
    intro s
    induction s using Finset.cons_induction with
    | empty =>
      exact eig_one om χT χS f (a0 k) (b0 k') (cut_empty hε x) (cut_empty hε y)
    | cons v s hv ih =>
      exact eig_mul om χT χS (hloc v) ih (a1 v s hv k) (b1 v s hv k') (cut_cons hε hv x) (cut_cons hε hv y)
  exact eig_limit om χT χS (hW.om_cont f hth) hW.hecT.1 hW.hecS.1 (a3 k hg) (b3 k' hh) (tendsto_cut hε hx)
    (tendsto_cut hε hy) hfin

end GlobalTheory.FinVac

end
