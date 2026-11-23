import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCharsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplitStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfPowEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem exists_int_lift {L K : Type} [AddCommGroup L] [Module.Projective ℤ L] [Field K] {q : ℕ} (hq : q ≠ 0)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ q) (g : L → Kˣ) (hg : ∀ a b, g (a + b) = g a * g b) (hgq : ∀ a, g a ^ q = 1) :
    ∃ f : L →ₗ[ℤ] ℤ, ∀ b, g b = ζ ^ f b := by
  haveI : NeZero q := ⟨hq⟩
  have hm : ∀ a, g a ∈ Subgroup.zpowers ζ := fun a => by
    rw [hζ.zpowers_eq]
    exact (mem_rootsOfUnity _ _).2 (hgq a)
  let G : L →+ Additive (Subgroup.zpowers ζ) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul ⟨g a, hm a⟩) fun a b => congrArg Additive.ofMul (Subtype.ext (hg a b))
  let π : ℤ →+ Additive (Subgroup.zpowers ζ) :=
    AddMonoidHom.mk' (fun k => Additive.ofMul ⟨ζ ^ k, k, rfl⟩) fun a b =>
      congrArg Additive.ofMul (Subtype.ext (zpow_add ζ a b))
  obtain ⟨f, hf⟩ := Module.projective_lifting_property π.toIntLinearMap G.toIntLinearMap (by
    rintro ⟨_, k, rfl⟩
    exact ⟨k, rfl⟩)
  exact ⟨f, fun b => (congrArg (fun z => (z.toMul : Kˣ)) (LinearMap.congr_fun hf b)).symm⟩

private theorem exists_label {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {R K : Type} [CommRing R] [Field K] {io : R →+* K}
    (hio : Function.Injective io) {x : Sp R ⟶ Z.X} {y : Sp K ⟶ Xo.XF c} {q : ℕ} (hq : q ≠ 0)
    {ch : Dw.La → TorsChar Z.t x q} (hW : WeilLab Z io x y q ch) (χ : GlobalTheory.HtGen.TorsK Z.t (y ≫ Z.j) q →* Kˣ) :
    ∃ a, GlobalTheory.HtGen.InducedBy χ x io (RingHom.id R) (ch a) := by
  obtain ⟨lb, ζ, ⟨hζ, hadd, -, hsur, -⟩, hch⟩ := hW
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.WeilTorsChar.exists_mulEquiv_points _ _ _ _ Z.m.cart (Over.mk y)
  let Ψ : (Over.mk y ⟶ Z.oF.t.G) ≃* (Over.mk (y ≫ Z.j) ⟶ Z.t.G) := Φ
  have hΨ : ∀ s, (Ψ s).left = s.left ≫ Z.m.φ := hΦ
  have ht : ∀ b, Ψ (lb b) ∈ GlobalTheory.HtGen.TorsK Z.t (y ≫ Z.j) q := fun b => by
    change Ψ (lb b) ^ q = 1
    rw [← map_pow, (hsur _).2 ⟨b, rfl⟩, map_one]
  haveI : Module.Projective ℤ Dw.La := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 Dw.proj
    exact Module.Projective.of_split (s.restrictScalars ℤ)
      ((Finsupp.linearCombination (𝓞 E) (id : Dw.La → Dw.La)).restrictScalars ℤ)
      (LinearMap.ext fun a => LinearMap.congr_fun hs a)
  obtain ⟨f, hf⟩ := exists_int_lift hq hζ (fun b => χ ⟨Ψ (lb b), ht b⟩) (fun a b => by
    rw [← map_mul]
    congr 1
    exact Subtype.ext ((congrArg Ψ (hadd a b)).trans (map_mul Ψ _ _))) (fun b => by
    rw [← map_pow, show (⟨Ψ (lb b), ht b⟩ : GlobalTheory.HtGen.TorsK Z.t (y ≫ Z.j) q) ^ q = 1 from Subtype.ext (ht b), map_one])
  obtain ⟨a, ha⟩ := Dw.unimod.2 f
  refine ⟨a, fun σ k r w hσ hk hw hr => ?_⟩
  have hk1 : Ψ.symm k.1 ^ q = 1 := by
    rw [← map_pow, show k.1 ^ q = 1 from k.2, map_one]
  obtain ⟨b, hb⟩ := (hsur _).1 hk1
  have hb' : Ψ (lb b) = k.1 := by rw [hb, MulEquiv.apply_symm_apply]
  have hid : spMap (RingHom.id R) = 𝟙 _ := GlobalTheory.TorsCharExt.sp_id R
  have hx : spMap (RingHom.id R) ≫ x = spMap (algebraMap R R) ≫ x := rfl
  have hw1 : w ^ q = 1 := by
    have : w = GlobalTheory.TorsCharExt.pull Z.t (spMap (RingHom.id R)) hx.symm σ := Over.OverMorphism.ext hw
    rw [this, ← map_pow, hσ, map_one]
  have h1 := hch a b w hw1 (by rw [← hΨ, hb', hk, hw, hid, Category.id_comp])
  apply hio
  rw [h1, RingHom.id_apply, hr, ha, ← hf b]
  congr 2
  exact Subtype.ext hb'

theorem UpperTheory.torsion_character_integral_point :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) [IsLocallyNoetherian Z.X], Z.X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (x : Sp ↥(intO ℂ_[p]) ⟶ Z.X) (y : Sp ℂ_[p] ⟶ Xo.XF c), 2 ≤ n → spMap (intO ℂ_[p]).subtype ≫ x = y ≫ Z.j → ∀ ch : Dw.La → TorsChar Z.t x (p ^ n), WeilLab Z (intO ℂ_[p]).subtype x y (p ^ n) ch → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ Z.t.G.left)) (h : Dw.La → Fin g → ↥(intO ℂ_[p])), IsTanBasis Z.t x e → (∀ a, DlogIs Z.t p n (ch a) e (h a)) → ∀ cf : Fin g → ℂ_[p], (cf ∈ latCo Z.t p (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) ↔ ∀ a, ‖∑ i, (h a i : ℂ_[p]) * cf i‖ ≤ 1) ∧ (cf ∈ latCo Z.t p (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) → ∀ i, ‖(p : ℂ_[p]) * cf i‖ ≤ 1) := by
  intro E _ _ _ H Dw l Xo c Z _ hX p hp n x y hn hxy ch hW g e h he hD cf
  classical
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hd : p ^ 2 ∣ p ^ n := pow_dvd_pow p hn
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  haveI := GlobalTheory.TorsCharExt.intO_valuationRing ℂ_[p]
  haveI := GlobalTheory.TorsCharExt.intO_isFractionRing ℂ_[p]
  haveI : IsIntegrallyClosed ↥(intO ℂ_[p]) := inferInstanceAs (IsIntegrallyClosed ↥(GlobalTheory.TorsCharExt.intV ℂ_[p]))
  have hζ : ∃ ζ : ℂ_[p], IsPrimitiveRoot ζ (p ^ n) := by
    obtain ⟨lb, ζ, ⟨hζ, -⟩, -⟩ := hW
    exact ⟨ζ, IsPrimitiveRoot.coe_units_iff.2 hζ⟩
  obtain ⟨hfin, hind⟩ := GlobalTheory.T.integral_point_extension_split E H Z.X Z.t ℂ_[p] (y ≫ Z.j) (p ^ n) hq hζ
    (GlobalTheory.HtGen.splitK_of_isAlgClosed Z.t _ hq) ↥(intO ℂ_[p]) x hxy
  obtain ⟨-, hex, hag⟩ := hind p (RingHom.id _) x inferInstance (by rw [GlobalTheory.TorsCharExt.sp_id, Category.id_comp])
  choose lab hlab using exists_label Z (intO ℂ_[p]).subtype_injective hq hW
  obtain ⟨N, ⟨eqv⟩⟩ := Finite.exists_equiv_fin (GlobalTheory.HtGen.TorsK Z.t (y ≫ Z.j) (p ^ n) →* ℂ_[p]ˣ)
  have heC := fun i => GlobalTheory.FactorDepth.isTanAtG_map Z.t (intO ℂ_[p]).subtype (he.1 i)
  obtain ⟨w, -, hw⟩ := Guard.exists_comb heC cf
  have hmem : cf ∈ latCo Z.t p (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) ↔
      w ∈ latHT Z.t p (spMap (intO ℂ_[p]).subtype ≫ x) :=
    ⟨fun ⟨w', h1, h2⟩ => Guard.comb_unique heC h2 hw ▸ h1, fun h1 => ⟨w, h1, hw⟩⟩
  have key := fun a₀ : Dw.La =>
    GlobalTheory.T.tangent_basis_torsion_chars E H Z.X Z.t hX p x g e he (N + 1)
      (fun j => GlobalTheory.HTLevel.res hd (ch (Fin.cons (α := fun _ => Dw.La) a₀ (fun k => lab (eqv.symm k)) j)))
      (fun j => h (Fin.cons (α := fun _ => Dw.La) a₀ (fun k => lab (eqv.symm k)) j))
      (fun c' => by
        obtain ⟨c'', hc''⟩ := GlobalTheory.T.torsionChar_extends_divisible_level E H Z.X Z.t ℂ_[p] x (p ^ 2) (p ^ n) hq hd c'
        obtain ⟨χ, hχ⟩ := hex c''
        refine ⟨(eqv χ).succ, fun B _ _ _ v hv => ?_⟩
        have hv' : v ^ (p ^ n) = 1 := by
          obtain ⟨k, hk⟩ := hd
          rw [hk, pow_mul, hv, one_pow]
        rw [← hc'' B v hv, hag χ c'' _ hχ (hlab χ) B v hv', Fin.cons_succ, Equiv.symm_apply_apply]
        rfl)
      (fun j => GlobalTheory.HTLevel.dlog_down hn _ _ (fun _ _ _ _ _ _ => rfl) he.1 (hD _)) cf w hw
  rw [hmem]
  exact ⟨⟨fun hL a => (key a).1.1 hL 0, fun hA => (key 0).1.2 fun j => hA _⟩, (key 0).2⟩
