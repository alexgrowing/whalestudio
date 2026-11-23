import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LatticeEmbeddingHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective

noncomputable section

namespace GlobalTheory.DictPinCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase (Fin𝔸 Inf𝔸 toFin latAd latBase CongrAt half IsLatEmb crd vec IsModelOf IsOrthoFrame IsArchAt
  IsRatUnitary ratTo LatMark IsMarkStab IsLevelStab IsDictOf IsFamilyOf unitaryOver AdelicU AdPinU)
open scoped TensorProduct nonZeroDivisors Matrix

abbrev conjHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E).toRingEquiv.toRingHom

section First

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)

def gramOf : Matrix (Fin n) (Fin n) E := Matrix.of fun a b => hT (fr a) (fr b)

def latHat : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Fin𝔸 F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L0, z = fun i => a ⊗ₜ fr.repr x i}

def archM (th' : Inf𝔸 F ⊗[F] E →+* ℂ) (h : G) : Matrix (Fin n) (Fin n) ℂ := (infHom h).1.map th'

def finVec (v : Fin n → E) : Fin n → Fin𝔸 F ⊗[F] E := fun i => (1 : Fin𝔸 F) ⊗ₜ v i

def gLat (g : G) : Set (Fin n → Fin𝔸 F ⊗[F] E) :=
  (finHom g).1.mulVec '' (latHat F fr L0 : Set (Fin n → Fin𝔸 F ⊗[F] E))

def latG (g : G) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {w | ∃ a : E, a ∈ AA ∧ ∃ v, finVec F v ∈ gLat F fr L0 finHom g ∧ w = a • v}

def latGHat (g : G) : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E) :=
  AddSubgroup.closure {w | ∃ a : E, a ∈ AA ∧ ∃ z ∈ gLat F fr L0 finHom g,
    w = fun i => ((1 : Fin𝔸 F) ⊗ₜ a) * z i}

def LatEmb {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin n → E)) : Prop :=
  Function.Injective ι ∧ LinearMap.range ι = latG F fr L0 AA finHom 1

def LatIsom {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La)
    (ι : La →ₗ[𝓞 E] (Fin n → E)) : Prop :=
  ∃ ε : ℤˣ, ∀ x y, ((EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) *
    Algebra.trace ℚ E (xi0 * hT (fr.equivFun.symm (ι x)) (fr.equivFun.symm (ι y)))

def ModelW (hr : n = r) (X : Data E r) : Prop :=
  X.Gm = -(Matrix.reindex (finCongr hr) (finCongr hr) (gramOf fr hT)).transpose ∧ X.ξ0 = -xi0

def IsOrthogonalFrame (X : Data E r) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ ∈ X.Ψ, gram τ X.Gm (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def halfVec (b : 𝓞 E) (z : Fin n → Fin𝔸 F ⊗[F] E) : Fin n → Fin𝔸 F ⊗[F] E :=
  fun i => ((1 : Fin𝔸 F) ⊗ₜ (b : E)) * z i

def KfHalf (Kf : Subgroup G) (M : ℕ) (Mh : Ideal (𝓞 E)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC ∧ ∀ b ∈ Mh, ∀ z ∈ latHat F fr L0, ∃ y ∈ latHat F fr L0,
    (finHom k).1.mulVec (halfVec F b z) - halfVec F b z = M • y

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

open Classical in

def DictLat (U : Unf Xo c σ r) (hr : n = r) (dict : G → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 E] (Fin n → E)) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Inf𝔸 F ⊗[F] E →+* ℂ))
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ((∀ k a b, (((Fm.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E
        (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (Fm.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
      IsPeriod (Fm.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = Fm.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (Fm.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)) ∧
    ∀ h : G, ∃ γ ∈ GQ,
      ((U.X (dict h).1).Λ : Set (Fin r → E)) =
        (fun v : Fin n → E => v ∘ Fin.cast hr.symm) '' (latG F fr L0 AA finHom (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        ∃ w ∈ latGHat F fr L0 AA finHom (γ * h),
        finVec F ((φ (dict h).1 (Fm.t (ik (dict h).1) a) : Fin r → E) ∘ Fin.cast hr) -
          (finHom (γ * h)).1.mulVec (finVec F (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM F infHom (th (dict h).1 τ) (γ * h)) * x₀ τ.1

def AdPinWith (U : Unf Xo c σ r) (dict : G → Σ k, Frame (U.X k).Ψ r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (Q : ∀ k, (Dw.La → (U.X k).Λ) → Prop) : Prop :=
  ∃ (hr : n = r)
    (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun i => relab c σ (e i).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Inf𝔸 F ⊗[F] E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι₀
    (LatEmb F fr L0 AA finHom ι ∧ LatIsom fr hT xi0 Dw.EF ι ∧ (∀ k τ, IsArchAt F τ.1 (th k τ)) ∧
      DictLat F fr L0 AA infHom finHom GQ U hr dict ι e Fm ik φ th x₀) ∧
    ∀ k, Q k fun a => φ k (Fm.t (ik k) a)

def AdPin (U : Unf Xo c σ r) (dict : G → Σ k, Frame (U.X k).Ψ r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∃ (hr : n = r)
    (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun i => relab c σ (e i).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Inf𝔸 F ⊗[F] E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι₀
    LatEmb F fr L0 AA finHom ι ∧ LatIsom fr hT xi0 Dw.EF ι ∧ (∀ k τ, IsArchAt F τ.1 (th k τ)) ∧
      DictLat F fr L0 AA infHom finHom GQ U hr dict ι e Fm ik φ th x₀

def TypeClause (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (q : ℕ) (X : Data E r) : Prop :=
  X.p0 = q ∧ ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0

def flipForm (x y : W) : E := hT y x

def IsRatPoints : Prop :=
  (∀ γ ∈ GQ, ∃ γ₀, IsRatUnitary fr (flipForm hT) γ₀ ∧ finHom γ = ratTo F (Fin𝔸 F) γ₀ ∧ infHom γ = ratTo F (Inf𝔸 F) γ₀) ∧
    ∀ γ₀, IsRatUnitary fr (flipForm hT) γ₀ →
      ∃ γ ∈ GQ, finHom γ = ratTo F (Fin𝔸 F) γ₀ ∧ infHom γ = ratTo F (Inf𝔸 F) γ₀

end First

section Compare

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)

def coord : W ≃ₗ[𝓞 E] (Fin n → E) := fr.equivFun.restrictScalars (𝓞 E)

theorem finVec_coord (v : W) : finVec F (coord fr v) = toFin F fr v := rfl

theorem latHat_eq : latHat F fr L0 = GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := rfl

theorem latGHat_eq (g : G) : latGHat F fr L0 AA finHom g = latAd F fr L0 (AA : Submodule (𝓞 E) E) (finHom g) := by
  unfold latGHat latAd
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨a, ha, z, hz, rfl⟩
  · rintro ⟨a, ha, z, hz, rfl⟩
    exact ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩

theorem coord_smul (a : E) (v : W) : coord fr (a • v) = a • coord fr v := fr.equivFun.map_smul a v

theorem latG_eq (g : G) : latG F fr L0 AA finHom g =
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG F fr L0 (AA : Submodule (𝓞 E) E) (finHom g)).map (coord fr).toLinearMap := by
  unfold latG GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, v, ⟨z, hz, hv⟩, rfl⟩
    obtain ⟨x, rfl⟩ := (coord fr).surjective v
    exact ⟨a • x, ⟨a, ha, x, ⟨z, hz, hv.symm⟩, rfl⟩, coord_smul fr a x⟩
  · rintro ⟨_, ⟨a, ha, x, ⟨z, hz, hv⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, coord fr x, ⟨z, hz, hv.symm⟩, coord_smul fr a x⟩

theorem mem_latG_iff (g : G) (v : W) : coord fr v ∈ latG F fr L0 AA finHom g ↔
    v ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG F fr L0 (AA : Submodule (𝓞 E) E) (finHom g) := by
  rw [latG_eq]
  constructor
  · rintro ⟨x, hx, h⟩
    rwa [← (coord fr).injective h]
  · exact fun h => ⟨v, h, rfl⟩

theorem latHat_eq_hat : GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 =
    GlobalTheory.AdLat.hat F ((L0.map (coord fr).toLinearMap : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat GlobalTheory.AdLat.hat
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, ha, x, hx, rfl⟩

theorem span_coord (hsp : Submodule.span E (L0 : Set W) = ⊤) :
    Submodule.span E ((L0.map (coord fr).toLinearMap : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
  have h : ((L0.map (coord fr).toLinearMap : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
      fr.equivFun.toLinearMap '' (L0 : Set W) := rfl
  rw [h, ← Submodule.map_span, hsp, Submodule.map_top, LinearEquiv.range]

theorem latG_one (hfg : L0.FG) (hsp : Submodule.span E (L0 : Set W) = ⊤) (𝔄 : Submodule (𝓞 E) E) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG F fr L0 𝔄 1 = latBase L0 𝔄 := by
  refine le_antisymm (Submodule.span_mono ?_) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latBase_le_latG_one F fr L0 𝔄)
  rintro _ ⟨a, ha, x, ⟨z, hz, hx⟩, rfl⟩
  refine ⟨a, ha, x, ?_, rfl⟩
  rw [Units.val_one, Matrix.one_mulVec] at hx
  rw [← hx, latHat_eq_hat] at hz
  obtain ⟨y, hy, h⟩ := ((GlobalTheory.AdLat.hat_rational_points_and_approx F E n _ (hfg.map _) (span_coord fr L0 hsp)).1
    (coord fr x)).1 hz
  rwa [← (coord fr).injective h]

theorem trace_flip (hherm : ∀ x y, cc (hT x y) = hT y x) (hxi : cc xi0 = -xi0) (x y : W) :
    Algebra.trace ℚ E (xi0 * flipForm hT x y) = -Algebra.trace ℚ E (xi0 * hT x y) := by
  have h := Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) (xi0 * hT x y)
  rw [← h, ← map_neg]
  congr 1
  show xi0 * hT y x = -(IsCMField.complexConj E (xi0 * hT x y))
  rw [map_mul, ← hherm x y]
  unfold cc at hxi ⊢
  rw [hxi]; ring

theorem latEmb_iff {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (hfg : L0.FG)
    (hsp : Submodule.span E (L0 : Set W) = ⊤) (hherm : ∀ x y, cc (hT x y) = hT y x) (hxi : cc xi0 = -xi0)
    (ι : Dw.La →ₗ[𝓞 E] W) :
    (LatEmb F fr L0 AA finHom ((coord fr).toLinearMap ∘ₗ ι) ∧ LatIsom fr hT xi0 Dw.EF ((coord fr).toLinearMap ∘ₗ ι)) ↔
      IsLatEmb (flipForm hT) L0 (AA : Submodule (𝓞 E) E) xi0 Dw ι := by
  unfold LatEmb LatIsom IsLatEmb
  rw [and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact (coord fr).injective.of_comp_iff ι
  · rw [latG_eq, map_one, latG_one fr L0 hfg hsp, LinearMap.range_comp]
    exact (Submodule.map_injective_of_injective (coord fr).injective).eq_iff
  · have e : ∀ x, fr.equivFun.symm (((coord fr).toLinearMap ∘ₗ ι) x) = ι x := fun x => fr.equivFun.symm_apply_apply _
    simp only [e, trace_flip hT xi0 hherm hxi]
    constructor <;> rintro ⟨ε, h⟩ <;> refine ⟨-ε, fun x y => ?_⟩ <;> rw [h] <;> simp

theorem hT_expand (y x : W) : hT y x = ∑ a, ∑ b, fr.repr x a * gramOf fr hT b a * cc (fr.repr y b) := by
  conv_lhs => rw [← fr.sum_repr y, ← fr.sum_repr x]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  show fr.repr x a * (cc (fr.repr y b) * hT (fr b) (fr a)) = fr.repr x a * hT (fr b) (fr a) * cc (fr.repr y b)
  ring

theorem model_iff (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (hr : n = r) (q : ℕ) (X : Data E r)
    (hsgn : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ xi0).im) :
    (ModelW fr hT xi0 hr X ∧ TypeClause H q X) ↔ IsModelOf H hr fr (flipForm hT) xi0 q X := by
  subst hr
  have hG : X.Gm = -(Matrix.reindex (finCongr rfl) (finCongr rfl) (gramOf fr hT)).transpose ↔
      ∀ x y : W, herm X.Gm (crd rfl fr x) (crd rfl fr y) = -flipForm hT x y := by
    constructor
    · intro h x y
      rw [h, flipForm, hT_expand fr hT y x, herm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [crd]
    · intro h
      ext a b
      have := h (fr a) (fr b)
      simp [herm, crd, Finsupp.single_apply, cc, apply_ite, flipForm] at this
      simp [gramOf, this]
  unfold ModelW TypeClause IsModelOf
  rw [hG]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, h3, h4, Or.inr h2, fun τ hτ => ?_⟩
    rw [h2, map_neg, Complex.neg_im]
    exact neg_neg_of_pos (hsgn τ ((h4 τ).1 hτ))
  · rintro ⟨h1, h3, h4, h2, h5⟩
    refine ⟨⟨h1, h2.resolve_left fun h => ?_⟩, h3, h4⟩
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases hτ : τ ∈ X.Ψ
      · exact ⟨τ, hτ⟩
      · exact ⟨_, not_not.1 fun h' => hτ ((X.cmType τ).2 h')⟩
    have := h5 τ hτ
    rw [h] at this
    exact lt_asymm this (hsgn τ ((h4 τ).1 hτ))

theorem orthogonal_frame_iff (X : Data E r) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : IsOrthogonalFrame X x₀ ↔ IsOrthoFrame X x₀ :=
  Iff.rfl

def fixMod {R : Type} [CommRing R] (k : Matrix (Fin n) (Fin n) R) (M : ℕ) (P : AddSubgroup (Fin n → R)) :
    AddSubgroup (Fin n → R) where
  carrier := {v | ∃ y ∈ P, k *ᵥ v - v = M • y}
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro v w ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y + y', add_mem hy hy', by rw [Matrix.mulVec_add, smul_add, ← h, ← h']; abel⟩
  neg_mem' := by
    rintro v ⟨y, hy, h⟩
    exact ⟨-y, neg_mem hy, by rw [Matrix.mulVec_neg, smul_neg, ← h]; abel⟩

theorem fixMod_smul {R : Type} [CommRing R] {k : Matrix (Fin n) (Fin n) R} {M : ℕ} {P P' : AddSubgroup (Fin n → R)}
    (s : R) (hs : ∀ y ∈ P, s • y ∈ P') {v : Fin n → R} (hv : v ∈ fixMod k M P) : s • v ∈ fixMod k M P' := by
  obtain ⟨y, hy, h⟩ := hv
  exact ⟨s • y, hs y hy, by rw [Matrix.mulVec_smul, ← smul_sub, h, smul_comm]⟩

theorem mem_fixMod_iff {R : Type} [CommRing R] {k : Matrix (Fin n) (Fin n) R} {M : ℕ} {P : AddSubgroup (Fin n → R)}
    {v : Fin n → R} : v ∈ fixMod k M P ↔ ∃ y ∈ P, v - k *ᵥ v = M • y := by
  constructor <;> rintro ⟨y, hy, h⟩ <;> exact ⟨-y, neg_mem hy, by rw [smul_neg, ← h, neg_sub]⟩

abbrev ad (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] (a : E) : Fin𝔸 F ⊗[F] E := 1 ⊗ₜ a

omit [NumberField E] [IsCMField E] in
theorem ad_mul (a b : E) : ad F (a * b) = ad F a * ad F b := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit [IsCMField E] in
theorem mem_of_mul_inv {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {P : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E)}
    {z : Fin n → Fin𝔸 F ⊗[F] E} (h : ∀ a ∈ I, ∀ b ∈ I⁻¹, ad F (a * b) • z ∈ P) : z ∈ P := by
  have key : ∀ c ∈ I * I⁻¹, ad F c • z ∈ P := fun c hc =>
    FractionalIdeal.mul_induction_on hc h fun x y hx hy => by
      rw [ad, TensorProduct.tmul_add, add_smul]; exact add_mem hx hy
  have := key 1 (by rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _)
  rwa [ad, ← Algebra.TensorProduct.one_def, one_smul] at this

theorem mul_inv_smul_mem {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {a b : E} (ha : a ∈ I) (hb : b ∈ I⁻¹)
    {z : Fin n → Fin𝔸 F ⊗[F] E} (hz : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) :
    ad F (a * b) • z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := by
  have hab : a * b ∈ I * I⁻¹ := FractionalIdeal.mul_mem_mul ha hb
  rw [mul_inv_cancel₀ hI, FractionalIdeal.mem_one_iff] at hab
  obtain ⟨s, hs⟩ := hab
  rw [latHat_eq_hat] at hz ⊢
  rw [← hs]
  exact GlobalTheory.AdLat.Translate.hat_smul_ring _ s hz

omit [NumberField E] [IsCMField E] [IsScalarTower (𝓞 E) E W] in
theorem toFin_smul (a : E) (x : W) : toFin F fr (a • x) = ad F a • toFin F fr x := by
  funext i
  simp [toFin, Algebra.TensorProduct.tmul_mul_tmul]

omit [NumberField E] [IsCMField E] [IsScalarTower (𝓞 E) E W] in
theorem toFin_mem {x : W} (hx : x ∈ L0) : toFin F fr x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, x, hx, rfl⟩

omit [IsCMField E] in
theorem smul_mem_latAd_one {a : E} (ha : a ∈ AA) {z : Fin n → Fin𝔸 F ⊗[F] E}
    (hz : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) : ad F a • z ∈ latAd F fr L0 (AA : Submodule (𝓞 E) E) 1 :=
  AddSubgroup.subset_closure ⟨a, ha, z, hz, by rw [Units.val_one, Matrix.one_mulVec]⟩

theorem inv_smul_mem_latHat (hA : AA ≠ 0) {b : E} (hb : b ∈ AA⁻¹) {w : Fin n → Fin𝔸 F ⊗[F] E}
    (hw : w ∈ latAd F fr L0 (AA : Submodule (𝓞 E) E) 1) : ad F b • w ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hw
    rw [Units.val_one, Matrix.one_mulVec, smul_smul, ← ad_mul, mul_comm]
    exact mul_inv_smul_mem fr L0 hA ha hb hz
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

omit [NumberField E] [IsCMField E] in
theorem halfVec_eq (b : 𝓞 E) (z : Fin n → Fin𝔸 F ⊗[F] E) : halfVec F b z = ad F (algebraMap (𝓞 E) E b) • z := rfl

def FixesHalf (k : Matrix (Fin n) (Fin n) (Fin𝔸 F ⊗[F] E)) (M : ℕ) (Mh : Ideal (𝓞 E)) : Prop :=
  ∀ b ∈ Mh, ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0,
    ad F (algebraMap (𝓞 E) E b) • z ∈ fixMod k M (GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0)

theorem FixesHalf.mulVec_mem {k : Matrix (Fin n) (Fin n) (Fin𝔸 F ⊗[F] E)} {M : ℕ} {Mh : Ideal (𝓞 E)}
    (h : FixesHalf fr L0 k M Mh) (hM : (M : 𝓞 E) ∈ Mh) (hM0 : M ≠ 0) :
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := by
  have hI : (Mh : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h0 => hM0 (by rw [h0, Ideal.mem_bot] at hM; exact_mod_cast hM)
  intro z hz
  refine mem_of_mul_inv hI fun a ha b hb => ?_
  obtain ⟨a', ha', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
  obtain ⟨y, hy, e⟩ := h a' ha' z hz
  have eM : ad F (algebraMap (𝓞 E) E (M : 𝓞 E)) = (M : Fin𝔸 F ⊗[F] E) := by
    rw [map_natCast]
    exact map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] Fin𝔸 F ⊗[F] E) M
  have e' : ad F (algebraMap (𝓞 E) E a' * b) • k *ᵥ z =
      ad F (algebraMap (𝓞 E) E a' * b) • z + ad F (algebraMap (𝓞 E) E (M : 𝓞 E) * b) • y := by
    rw [Matrix.mulVec_smul, sub_eq_iff_eq_add'] at e
    rw [mul_comm _ b, mul_comm _ b, ad_mul, ad_mul, mul_smul, mul_smul, mul_smul, ← smul_add, e, eM,
      Nat.cast_smul_eq_nsmul]
  rw [e']
  exact add_mem (mul_inv_smul_mem fr L0 hI ha hb hz)
    (mul_inv_smul_mem fr L0 hI (FractionalIdeal.mem_coeIdeal_of_mem _ hM) hb hy)

omit [IsCMField E] in
theorem latAd_eq_of_stab {k : GL (Fin n) (Fin𝔸 F ⊗[F] E)}
    (h1 : ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k.1 *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0)
    (h2 : ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k⁻¹.1 *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) :
    latAd F fr L0 (AA : Submodule (𝓞 E) E) k = latAd F fr L0 (AA : Submodule (𝓞 E) E) 1 := by
  refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ((AddSubgroup.closure_le _).2 ?_)
  · rintro _ ⟨a, ha, z, hz, rfl⟩
    exact smul_mem_latAd_one fr L0 AA ha (h1 z hz)
  · rintro _ ⟨a, ha, z, hz, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, _, h2 z hz, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]

omit [NumberField E] [IsCMField E] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] in
theorem toFin_add (x y : W) : toFin F fr (x + y) = toFin F fr x + toFin F fr y := by
  funext i
  simp [toFin, TensorProduct.tmul_add]

omit [NumberField E] [IsCMField E] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] in
theorem toFin_zero : toFin F fr (0 : W) = 0 := by
  funext i
  simp [toFin]

theorem FixesHalf.base {k : Matrix (Fin n) (Fin n) (Fin𝔸 F ⊗[F] E)} {M : ℕ} {Mh : Ideal (𝓞 E)}
    (h : FixesHalf fr L0 k M Mh) {u : W} (hu : u ∈ latBase L0 (AA : Submodule (𝓞 E) E)) : ∀ b ∈ Mh,
    toFin F fr (b • u) ∈ fixMod k M (latAd F fr L0 (AA : Submodule (𝓞 E) E) 1) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hu
    intro b hb
    rw [← algebraMap_smul E b, smul_comm, toFin_smul, toFin_smul]
    exact fixMod_smul _ (fun y hy => smul_mem_latAd_one fr L0 AA ha hy) (h b hb _ (toFin_mem fr L0 hx))
  | zero =>
    intro b _
    rw [smul_zero, toFin_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro b hb
    rw [smul_add, toFin_add]
    exact add_mem (hx b hb) (hy b hb)
  | smul s x _ hx =>
    intro b hb
    rw [smul_smul]
    exact hx _ (Mh.mul_mem_right s hb)

theorem fixesHalf_of_base (hA : AA ≠ 0) {k : Matrix (Fin n) (Fin n) (Fin𝔸 F ⊗[F] E)} {M : ℕ} {Mh : Ideal (𝓞 E)}
    (h : ∀ u ∈ latBase L0 (AA : Submodule (𝓞 E) E), ∀ b ∈ Mh,
      toFin F fr (b • u) ∈ fixMod k M (latAd F fr L0 (AA : Submodule (𝓞 E) E) 1)) : FixesHalf fr L0 k M Mh := by
  intro b hb z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨t, ht, x, hx, rfl⟩ := hz
    have e : (fun i => t ⊗ₜ[F] fr.repr x i) = (t ⊗ₜ[F] (1 : E) : Fin𝔸 F ⊗[F] E) • toFin F fr x :=
      GlobalTheory.AdLat.Translate.gen_eq t (coord fr x)
    rw [e, smul_comm]
    refine fixMod_smul (P := GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0) _ (fun y hy => ?_)
      (mem_of_mul_inv hA fun a ha a' ha' => ?_)
    · rw [latHat_eq_hat] at hy ⊢
      exact GlobalTheory.AdLat.Translate.hat_smul_int ht hy
    · have h5 := h (a • x) (Submodule.subset_span ⟨a, ha, x, hx, rfl⟩) b hb
      rw [← algebraMap_smul E b, smul_comm, toFin_smul, toFin_smul] at h5
      rw [mul_comm, ad_mul, mul_smul]
      exact fixMod_smul _ (fun y hy => inv_smul_mem_latHat fr L0 AA hA ha' hy) h5
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem level_elem_iff {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H) (hfg : L0.FG)
    (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0) (ι : Dw.La →ₗ[𝓞 E] W)
    (hι : LinearMap.range ι = latBase L0 (AA : Submodule (𝓞 E) E)) (cj : E ≃ₐ[F] E)
    (k : GL (Fin n) (Fin𝔸 F ⊗[F] E)) (hdet : k.1.det * GlobalTheory.AdLat.sg (Fin𝔸 F) cj k.1.det = 1) :
    FixesHalf fr L0 k.1 l.M (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ↔
      latAd F fr L0 (AA : Submodule (𝓞 E) E) k = latAd F fr L0 (AA : Submodule (𝓞 E) E) 1 ∧
        ∀ a ∈ half Dw l, CongrAt F fr L0 (AA : Submodule (𝓞 E) E) l.M k (ι a) (ι a) := by
  constructor
  · intro h
    have hM : (l.M : 𝓞 E) ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      have h0 := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
      rw [← l.prod] at h0
      exact (Ideal.mem_inf.1 (Ideal.mul_le_inf (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h0)).2
    have h1 := h.mulVec_mem fr L0 hM (by have := l.three_le; omega)
    have h2 : ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0, k⁻¹.1 *ᵥ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0 := by
      rw [latHat_eq_hat] at h1 ⊢
      exact GlobalTheory.AdLat.inv_mulVec_mem_hat F E n _ k cj (hfg.map _) (span_coord fr L0 hsp) h1 hdet
    have h3 := latAd_eq_of_stab fr L0 AA h1 h2
    refine ⟨h3, fun a ha => ?_⟩
    unfold CongrAt
    rw [h3, ← mem_fixMod_iff]
    refine Submodule.smul_induction_on (p := fun a => toFin F fr (ι a) ∈ fixMod k.1 l.M _) ha (fun b hb x _ => ?_)
      fun x y hx hy => ?_
    · rw [map_smul]
      exact h.base fr L0 AA (by rw [← hι]; exact LinearMap.mem_range_self ι x) b hb
    · rw [map_add, toFin_add]
      exact add_mem hx hy
  · rintro ⟨h3, h⟩
    refine fixesHalf_of_base fr L0 AA hA fun u hu b hb => ?_
    rw [← hι] at hu
    obtain ⟨x, rfl⟩ := hu
    have h5 := h (b • x) (Submodule.smul_mem_smul hb Submodule.mem_top)
    unfold CongrAt at h5
    rwa [h3, ← mem_fixMod_iff, map_smul] at h5

theorem mem_unitaryOver_iff (cj : E ≃ₐ[F] E) (h : W → W → E) (A : Type) [CommRing A] [Algebra F A]
    (g : GL (Fin n) (A ⊗[F] E)) : g ∈ unitaryOver F cj fr h A ↔
      g.1ᵀ * (Matrix.of fun a b => (1 : A) ⊗ₜ[F] h (fr a) (fr b)) * g.1.map (GlobalTheory.AdLat.sg A cj) =
        Matrix.of fun a b => (1 : A) ⊗ₜ[F] h (fr a) (fr b) := by
  set B : Matrix (Fin n) (Fin n) (A ⊗[F] E) := Matrix.of fun a b => (1 : A) ⊗ₜ[F] h (fr a) (fr b) with hB
  have e : ∀ (C : Matrix (Fin n) (Fin n) (A ⊗[F] E)) x y,
      ∑ a, ∑ b, x a * C a b * GlobalTheory.AdLat.sg A cj (y b) = x ⬝ᵥ C *ᵥ (GlobalTheory.AdLat.sg A cj ∘ y) := fun C x y => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Function.comp]
  have e2 : ∀ x y, (g.1 *ᵥ x) ⬝ᵥ B *ᵥ (GlobalTheory.AdLat.sg A cj ∘ (g.1 *ᵥ y)) =
      x ⬝ᵥ (g.1ᵀ * B * g.1.map (GlobalTheory.AdLat.sg A cj)) *ᵥ (GlobalTheory.AdLat.sg A cj ∘ y) := fun x y => by
    have : GlobalTheory.AdLat.sg A cj ∘ (g.1 *ᵥ y) = g.1.map (GlobalTheory.AdLat.sg A cj) *ᵥ (GlobalTheory.AdLat.sg A cj ∘ y) :=
      funext fun i => RingHom.map_mulVec (GlobalTheory.AdLat.sg A cj).toRingHom g.1 y i
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]
  change (∀ x y, ∑ a, ∑ b, (g.1 *ᵥ x) a * B a b * GlobalTheory.AdLat.sg A cj ((g.1 *ᵥ y) b) =
    ∑ a, ∑ b, x a * B a b * GlobalTheory.AdLat.sg A cj (y b)) ↔ _
  simp only [e, e2]
  refine ⟨fun hh => ?_, fun hh x y => by rw [hh]⟩
  ext a b
  have e3 : GlobalTheory.AdLat.sg A cj ∘ (Pi.single b 1 : Fin n → A ⊗[F] E) = Pi.single b 1 := by
    funext i
    by_cases hi : i = b <;> simp [hi]
  have := hh (Pi.single a 1) (Pi.single b 1)
  simpa [e3] using this

theorem det_of_unitary (cj : E ≃ₐ[F] E) (hnd : (gramOf fr hT).det ≠ 0) (A : Type) [CommRing A] [Algebra F A]
    {g : GL (Fin n) (A ⊗[F] E)} (hg : g ∈ unitaryOver F cj fr (flipForm hT) A) :
    g.1.det * GlobalTheory.AdLat.sg A cj g.1.det = 1 := by
  have h := congrArg Matrix.det ((mem_unitaryOver_iff fr cj _ A g).1 hg)
  have hB : (Matrix.of fun a b => (1 : A) ⊗ₜ[F] flipForm hT (fr a) (fr b)) =
      (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E).toRingHom.mapMatrix (gramOf fr hT)ᵀ := rfl
  have hu : IsUnit (Matrix.of fun a b => (1 : A) ⊗ₜ[F] flipForm hT (fr a) (fr b)).det := by
    rw [hB, ← RingHom.map_det, Matrix.det_transpose]
    exact (IsUnit.mk0 _ hnd).map _
  have hs : (g.1.map (GlobalTheory.AdLat.sg A cj)).det = GlobalTheory.AdLat.sg A cj g.1.det :=
    (RingHom.map_det (GlobalTheory.AdLat.sg A cj).toRingHom g.1).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs] at h
  refine hu.mul_left_cancel ?_
  rw [mul_one]
  linear_combination h

theorem level_iff {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H) (hfg : L0.FG)
    (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0) (hnd : (gramOf fr hT).det ≠ 0) (cj : E ≃ₐ[F] E)
    (hU : ∀ g, finHom g ∈ unitaryOver F cj fr (flipForm hT) (Fin𝔸 F)) (hGf : ∀ k, k ∈ GfC ↔ infHom k = 1)
    (ι : Dw.La →ₗ[𝓞 E] W) (hι : LinearMap.range ι = latBase L0 (AA : Submodule (𝓞 E) E)) (Kf : Subgroup G) :
    KfHalf F fr L0 finHom GfC Kf l.M (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ↔
      IsLevelStab F fr L0 (AA : Submodule (𝓞 E) E) l ι infHom finHom Kf := by
  refine forall_congr' fun k => iff_congr Iff.rfl (and_congr (hGf k) ?_)
  exact level_elem_iff fr L0 AA l hfg hsp hA ι hι cj _ (det_of_unitary fr hT cj hnd _ (hU k))

theorem latMark_iff {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (l : Level H) (hr : n = r)
    (ι : Dw.La →ₗ[𝓞 E] W) (X : Data E r) (mk : Dw.La → X.Λ) (g : G) :
    (((X.Λ : Set (Fin r → E)) =
        (fun v : Fin n → E => v ∘ Fin.cast hr.symm) '' (latG F fr L0 AA finHom g : Set _)) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w ∈ latGHat F fr L0 AA finHom g,
        finVec F ((mk a : Fin r → E) ∘ Fin.cast hr) -
          (finHom g).1.mulVec (finVec F (((coord fr).toLinearMap ∘ₗ ι) a)) = (l.M : ℕ) • w) ↔
      LatMark F hr fr L0 (AA : Submodule (𝓞 E) E) l ι X mk (finHom g) := by
  subst hr
  refine and_congr ?_ (forall₂_congr fun a _ => ?_)
  · have e : (fun v : Fin n → E => v ∘ Fin.cast (rfl : n = n).symm) = id := rfl
    rw [e, Set.image_id, SetLike.coe_set_eq, SetLike.ext_iff, (coord fr).surjective.forall]
    exact forall_congr' fun v => iff_congr Iff.rfl (mem_latG_iff fr L0 AA finHom g v)
  · have e : toFin F fr (vec rfl fr (mk a : Fin n → E)) = finVec F ((mk a : Fin n → E) ∘ Fin.cast rfl) := by
      have : vec rfl fr (mk a : Fin n → E) = fr.equivFun.symm (mk a : Fin n → E) := (fr.equivFun_symm_apply _).symm
      rw [this, ← finVec_coord]
      exact congrArg _ (fr.equivFun.apply_symm_apply _)
    unfold CongrAt
    rw [e, latGHat_eq]
    rfl

omit [IsCMField E] in
theorem isArchAt_unique [IsTotallyReal F] {τ : E →+* ℂ} {th th' : Inf𝔸 F ⊗[F] E →+* ℂ} (h : IsArchAt F τ th)
    (h' : IsArchAt F τ th') : th = th' := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x => rw [GlobalTheory.InfAdeleCM.hom_tmul τ th h.1 h.2, GlobalTheory.InfAdeleCM.hom_tmul τ th' h'.1 h'.2]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

theorem dictLat_iff (hQ : IsRatPoints F fr hT infHom finHom GQ) (U : Unf Xo c σ r) (hr : n = r)
    (dict : G → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] W) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : (E →+* ℂ) → (Inf𝔸 F ⊗[F] E →+* ℂ)) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) :
    DictLat F fr L0 AA infHom finHom GQ U hr dict ((coord fr).toLinearMap ∘ₗ ι) e Fm ik φ (fun _ τ => th τ.1) x₀ ↔
      IsFamilyOf U e Fm ik φ ∧ IsDictOf F hr fr (flipForm hT) L0 (AA : Submodule (𝓞 E) E) l ι U.X
        (fun k a => φ k (Fm.t (ik k) a)) th x₀ infHom finHom dict := by
  refine and_congr Iff.rfl (forall_congr' fun h => ?_)
  constructor
  · rintro ⟨γ, hγ, h1, h2, h3⟩
    obtain ⟨γ₀, hu, e1, e2⟩ := hQ.1 γ hγ
    refine ⟨γ₀, hu, ?_, ?_⟩
    · rw [← e1, ← map_mul]
      exact (latMark_iff fr L0 AA finHom l hr ι _ _ _).1 ⟨h1, h2⟩
    · rw [← e2, ← map_mul]
      exact h3
  · rintro ⟨γ₀, hu, h1, h3⟩
    obtain ⟨γ, hγ, e1, e2⟩ := hQ.2 γ₀ hu
    rw [← e1, ← map_mul] at h1
    rw [← e2, ← map_mul] at h3
    obtain ⟨h1, h2⟩ := (latMark_iff fr L0 AA finHom l hr ι _ _ _).2 h1
    exact ⟨γ, hγ, h1, h2, h3⟩

theorem adPinWith_true (U : Unf Xo c σ r) (dict : G → Σ k, Frame (U.X k).Ψ r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)) :
    AdPinWith F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ (fun _ _ => True) ↔
      AdPin F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ := by
  unfold AdPinWith AdPin
  simp only [implies_true, and_true]

theorem AdPinWith.adPin {U : Unf Xo c σ r} {dict : G → Σ k, Frame (U.X k).Ψ r}
    {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)} {Q : ∀ k, (Dw.La → (U.X k).Λ) → Prop}
    (h : AdPinWith F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ Q) :
    AdPin F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ := by
  obtain ⟨hr, g, e, Fm, ik, φ, th, h1, _⟩ := h
  exact ⟨hr, g, e, Fm, ik, φ, th, h1⟩

def embW (hr : n = r) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Dw.La →ₗ[𝓞 E] W :=
  (coord fr).symm.toLinearMap ∘ₗ LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι₀

theorem coord_embW (hr : n = r) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)) :
    (coord fr).toLinearMap ∘ₗ embW fr hr ι₀ = LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι₀ :=
  LinearMap.ext fun _ => (coord fr).apply_symm_apply _

theorem embW_surjective (hr : n = r) : Function.Surjective (embW (Dw := Dw) fr hr) := by
  subst hr
  exact fun ι => ⟨(coord fr).toLinearMap ∘ₗ ι, LinearMap.ext fun _ => (coord fr).symm_apply_apply _⟩

def SidePins (U : Unf Xo c σ r) (hr : n = r) (Kf : Subgroup G) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  (∀ k, ModelW fr hT xi0 hr (U.X k)) ∧ (∀ k, IsOrthogonalFrame (U.X k) x₀) ∧
    KfHalf F fr L0 finHom GfC Kf l.M (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ∧ ∀ k, TypeClause H Dw.q (U.X k)

section Joint

variable [IsTotallyReal F] (cj : E ≃ₐ[F] E) (hfg : L0.FG) (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0)
  (hherm : ∀ x y, cc (hT x y) = hT y x) (hnd : (gramOf fr hT).det ≠ 0) (hxi : cc xi0 = -xi0)
  (hsgn : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ xi0).im)
  (hU : ∀ g, finHom g ∈ unitaryOver F cj fr (flipForm hT) (Fin𝔸 F)) (hGf : ∀ k, k ∈ GfC ↔ infHom k = 1)
  (hQ : IsRatPoints F fr hT infHom finHom GQ)
  (U : Unf Xo c σ r) (hr : n = r) (dict : G → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup G)

include hfg hsp hA hherm hnd hxi hsgn hU hGf hQ

theorem joint_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.AdPin F hr fr (flipForm hT) L0 (AA : Submodule (𝓞 E) E) xi0 U infHom finHom dict Kf ↔
      ∃ x₀ ι₀, SidePins fr hT L0 xi0 finHom GfC U hr Kf x₀ ∧
        AdPinWith F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ fun k mk => IsMarkStab l (U.X k) mk ∧
          ∃ gk : G, LatMark F hr fr L0 (AA : Submodule (𝓞 E) E) l (embW fr hr ι₀) (U.X k) mk (finHom gk) := by
  constructor
  · rintro ⟨g, e, Fm, ik, φ, ι, th, x₀, h1, h2, h3, h4, h5, h6⟩
    obtain ⟨ι₀, rfl⟩ := embW_surjective fr hr ι
    have hm := fun k => (model_iff fr hT xi0 H hr Dw.q (U.X k) hsgn).2 (h4 k).1
    have hl := (latEmb_iff fr hT L0 AA xi0 finHom Dw hfg hsp hherm hxi _).2 h2
    have hd := (dictLat_iff fr hT L0 AA infHom finHom GQ hQ U hr dict _ e Fm ik φ th x₀).2 ⟨h1, h6⟩
    rw [coord_embW] at hl hd
    exact ⟨x₀, ι₀, ⟨fun k => (hm k).1, fun k => (h4 k).2.1,
      (level_iff fr hT L0 AA infHom finHom GfC l hfg hsp hA hnd cj hU hGf _ h2.2.1 Kf).2 h5, fun k => (hm k).2⟩,
      hr, g, e, Fm, ik, φ, fun _ τ => th τ.1, ⟨hl.1, hl.2, fun _ τ => h3 τ.1, hd⟩, fun k => (h4 k).2.2⟩
  · rintro ⟨x₀, ι₀, ⟨s1, s2, s3, s4⟩, hr', g, e, Fm, ik, φ, th, ⟨h1, h2, h3, h4⟩, h5⟩
    choose th' hth using fun τ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) τ
    obtain rfl : th = fun _ τ => th' τ.1 := funext fun k => funext fun τ => isArchAt_unique (h3 k τ) (hth τ.1)
    rw [← coord_embW fr] at h1 h2 h4
    have hl := (latEmb_iff fr hT L0 AA xi0 finHom Dw hfg hsp hherm hxi _).1 ⟨h1, h2⟩
    have hd := (dictLat_iff fr hT L0 AA infHom finHom GQ hQ U hr dict _ e Fm ik φ th' x₀).1 h4
    exact ⟨g, e, Fm, ik, φ, embW fr hr ι₀, th', x₀, hd.1, hl, hth,
      fun k => ⟨(model_iff fr hT xi0 H hr Dw.q (U.X k) hsgn).1 ⟨s1 k, s4 k⟩, s2 k, h5 k⟩,
      (level_iff fr hT L0 AA infHom finHom GfC l hfg hsp hA hnd cj hU hGf _ hl.2.1 Kf).1 s3, hd.2⟩

theorem first_of_second
    (h : GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.AdPin F hr fr (flipForm hT) L0 (AA : Submodule (𝓞 E) E) xi0 U infHom finHom dict Kf) :
    ∃ x₀ ι₀, SidePins fr hT L0 xi0 finHom GfC U hr Kf x₀ ∧ AdPin F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ := by
  obtain ⟨x₀, ι₀, h1, h2⟩ :=
    (joint_iff fr hT L0 AA xi0 infHom finHom GQ GfC cj hfg hsp hA hherm hnd hxi hsgn hU hGf hQ U hr dict Kf).1 h
  exact ⟨x₀, ι₀, h1, h2.adPin⟩

theorem joint_iff_of_onto (honto : ∀ k, ∃ g, (dict g).1 = k) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.AdPin F hr fr (flipForm hT) L0 (AA : Submodule (𝓞 E) E) xi0 U infHom finHom dict Kf ↔
      ∃ x₀ ι₀, SidePins fr hT L0 xi0 finHom GfC U hr Kf x₀ ∧
        AdPinWith F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀ fun k mk => IsMarkStab l (U.X k) mk := by
  rw [joint_iff fr hT L0 AA xi0 infHom finHom GQ GfC cj hfg hsp hA hherm hnd hxi hsgn hU hGf hQ U hr dict Kf]
  refine exists₂_congr fun x₀ ι₀ => and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨hr', g, e, Fm, ik, φ, th, h1, h2⟩
    exact ⟨hr', g, e, Fm, ik, φ, th, h1, fun k => (h2 k).1⟩
  · rintro ⟨hr', g, e, Fm, ik, φ, th, h1, h2⟩
    refine ⟨hr', g, e, Fm, ik, φ, th, h1, fun k => ⟨h2 k, ?_⟩⟩
    obtain ⟨h, rfl⟩ := honto k
    obtain ⟨γ, _, e1, e2, _⟩ := h1.2.2.2.2 h
    rw [← coord_embW fr] at e2
    exact ⟨γ * h, (latMark_iff fr L0 AA finHom l hr _ _ _ _).1 ⟨e1, e2⟩⟩

end Joint

theorem isMarkStab_iff {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (Fm : FamilyUnif Xo σ' ty) (i : Fin Fm.n)
    (X : Data E r) (φ : (Fm.Di i).La ≃ₗ[𝓞 E] X.Λ) :
    IsMarkStab l X (fun a => φ (Fm.t i a)) ↔ ∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (Fm.Di i).La), ∃ b : (Fm.Di i).La,
        γ.1 *ᵥ (φ a : Fin r → E) = (φ a : Fin r → E) + (l.M : ℕ) • (φ b : Fin r → E) := by
  refine forall_congr' fun γ => iff_congr Iff.rfl (and_congr_right fun hγ => ⟨fun h a ha => ?_, fun h a ha => ?_⟩)
  · have key : (φ a : Fin r → E) ∈ fixMod γ.1 l.M X.Λ.toAddSubgroup := by
      refine Submodule.smul_induction_on (p := fun a => (φ a : Fin r → E) ∈ fixMod γ.1 l.M X.Λ.toAddSubgroup) ha
        (fun b hb x _ => ?_) fun x y hx hy => ?_
      · obtain ⟨a', v, rfl⟩ := Fm.t_surj i x
        obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
        rw [smul_add, ← map_smul, map_add, Submodule.coe_add]
        refine add_mem (h _ (Submodule.smul_mem_smul hb Submodule.mem_top)) ?_
        rw [hm, smul_comm, mul_smul, map_nsmul, Submodule.coe_smul_of_tower]
        exact ⟨_, X.Λ.sub_mem ((hγ.2 _).1 (φ (m • b • v)).2) (φ (m • b • v)).2,
          by rw [smul_sub, ← Matrix.mulVec_smul]⟩
      · rw [map_add, Submodule.coe_add]
        exact add_mem hx hy
    obtain ⟨y, hy, e⟩ := key
    exact ⟨φ.symm ⟨y, hy⟩, by rw [φ.apply_symm_apply, ← e]; abel⟩
  · have ht : Fm.t i a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (Fm.Di i).La) := by
      have := Submodule.mem_map_of_mem (f := Fm.t i) ha
      rw [half, Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    obtain ⟨b, e⟩ := h _ ht
    exact ⟨_, (φ b).2, by rw [e]; abel⟩

def withGroup (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) (hle : Γ ≤ X.Γ)
    (hidx : ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab X.Gm X.Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ) (m : ℕ) (hm : 0 < m)
    (htr : ∀ ξ ∈ X.Λ, herm X.Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s →
      ∃ γ ∈ Γ, (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ ((m : E) * s * X.κ0)) : Data E r :=
  { X with
    Γ := Γ
    Γ_stab := fun γ h => X.Γ_stab γ (hle h)
    Γ_index := hidx
    Γ_free := fun γ h => X.Γ_free γ (hle h)
    χ_mul := fun la γ h γ' h' => X.χ_mul la γ (hle h) γ' (hle h')
    χ_add := fun la la' γ h => X.χ_add la la' γ (hle h)
    χ_fin := fun la => (X.χ_fin la).imp fun _ h => ⟨h.1, fun γ hγ => h.2 γ (hle hγ)⟩
    m := m
    m_pos := hm
    transv := htr }

theorem pins_withGroup (U : Unf Xo c σ r) (Γ : U.Comp → Subgroup (GL (Fin r) E)) (hle : ∀ k, Γ k ≤ (U.X k).Γ)
    (hidx : ∀ k, ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab (U.X k).Gm (U.X k).Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ k)
    (m : U.Comp → ℕ) (hm : ∀ k, 0 < m k)
    (htr : ∀ k, ∀ ξ ∈ (U.X k).Λ, herm (U.X k).Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s →
      ∃ γ ∈ Γ k, (γ : Matrix (Fin r) (Fin r) E) = transvMat (U.X k).Gm ξ ((m k : E) * s * (U.X k).κ0))
    (hr : n = r) (dict : G → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup G) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)) :
    let U' : Unf Xo c σ r := ⟨U.Comp, fun k => withGroup (U.X k) (Γ k) (hle k) (hidx k) (m k) (hm k) (htr k), U.un⟩
    ((SidePins fr hT L0 xi0 finHom GfC U' hr Kf x₀ ∧ AdPin F fr hT L0 AA xi0 infHom finHom GQ U' dict x₀ ι₀) ↔
      SidePins fr hT L0 xi0 finHom GfC U hr Kf x₀ ∧ AdPin F fr hT L0 AA xi0 infHom finHom GQ U dict x₀ ι₀) ∧
    ∀ k (mk : Dw.La → (U.X k).Λ), IsMarkStab l (U.X k) mk → (IsMarkStab l (U'.X k) mk ↔ Γ k = (U.X k).Γ) := by
  refine ⟨Iff.rfl, fun k mk h => ⟨fun h' => Subgroup.ext fun γ => (h' γ).trans (h γ).symm, fun e γ => ?_⟩⟩
  exact (by rw [e] : γ ∈ Γ k ↔ γ ∈ (U.X k).Γ).trans (h γ)

section Adelic

variable (cj : E ≃ₐ[F] E)

def infU (h : W → W → E) : AdelicU F cj fr h →* GL (Fin n) (Inf𝔸 F ⊗[F] E) :=
  (Subgroup.subtype _).comp (MonoidHom.fst _ _)

def finU (h : W → W → E) : AdelicU F cj fr h →* GL (Fin n) (Fin𝔸 F ⊗[F] E) :=
  (Subgroup.subtype _).comp (MonoidHom.snd _ _)

def ratU (h : W → W → E) : Subgroup (AdelicU F cj fr h) :=
  (MonoidHom.range ((Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeRight : E →ₐ[F] Inf𝔸 F ⊗[F] E).toRingHom).prod (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeRight : E →ₐ[F] Fin𝔸 F ⊗[F] E).toRingHom))).comap
    ((infU fr cj h).prod (finU fr cj h))

theorem isRatUnitary_iff (γ : GL (Fin n) E) : IsRatUnitary fr (flipForm hT) γ ↔
    γ.1ᵀ * (gramOf fr hT)ᵀ * γ.1.map cc = (gramOf fr hT)ᵀ := by
  have e : ∀ x y : Fin n → E, flipForm hT (fr.equivFun.symm x) (fr.equivFun.symm y) =
      x ⬝ᵥ (gramOf fr hT)ᵀ *ᵥ (cc ∘ y) := fun x y => by
    have h : ∀ (x : Fin n → E) a, fr.repr (fr.equivFun.symm x) a = x a := fun x a =>
      congrFun (fr.equivFun.apply_symm_apply x) a
    rw [flipForm, hT_expand fr]
    simp only [h, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Function.comp, Matrix.transpose_apply]
  have e2 : ∀ x y : Fin n → E, (γ.1 *ᵥ x) ⬝ᵥ (gramOf fr hT)ᵀ *ᵥ (cc ∘ (γ.1 *ᵥ y)) =
      x ⬝ᵥ (γ.1ᵀ * (gramOf fr hT)ᵀ * γ.1.map cc) *ᵥ (cc ∘ y) := fun x y => by
    have : cc ∘ (γ.1 *ᵥ y) = γ.1.map cc *ᵥ (cc ∘ y) := funext fun i => RingHom.map_mulVec (conjHom E) γ.1 y i
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]
  unfold IsRatUnitary
  simp only [e, e2]
  refine ⟨fun hh => ?_, fun hh x y => by rw [hh]⟩
  ext a b
  have e3 : cc ∘ (Pi.single b 1 : Fin n → E) = Pi.single b 1 := by
    funext i
    by_cases hi : i = b <;> simp [hi, cc]
  have := hh (Pi.single a 1) (Pi.single b 1)
  simpa [e3] using this

theorem ratTo_mem (hcj : ∀ x, cj x = cc x) (A : Type) [CommRing A] [Algebra F A]
    (γ : GL (Fin n) E) : (IsRatUnitary fr (flipForm hT) γ → ratTo F A γ ∈ unitaryOver F cj fr (flipForm hT) A) ∧
      (Nontrivial A → ratTo F A γ ∈ unitaryOver F cj fr (flipForm hT) A → IsRatUnitary fr (flipForm hT) γ) := by
  rw [mem_unitaryOver_iff, isRatUnitary_iff]
  set f := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E).toRingHom with hf
  have hB : (Matrix.of fun a b => (1 : A) ⊗ₜ[F] flipForm hT (fr a) (fr b)) = ((gramOf fr hT)ᵀ).map f := rfl
  have h1 : (ratTo F A γ).1ᵀ = (γ.1ᵀ).map f := rfl
  have h2 : (ratTo F A γ).1.map (GlobalTheory.AdLat.sg A cj) = (γ.1.map cc).map f := by
    ext a b
    show GlobalTheory.AdLat.sg A cj ((1 : A) ⊗ₜ[F] γ.1 a b) = (1 : A) ⊗ₜ[F] cc (γ.1 a b)
    rw [← hcj]
    rfl
  rw [hB, h1, h2, ← Matrix.map_mul, ← Matrix.map_mul]
  exact ⟨fun h => by rw [h], fun _ h => Matrix.map_injective f.injective h⟩

theorem isRatPoints_ratU (hcj : ∀ x, cj x = cc x) :
    IsRatPoints F fr hT (infU fr cj _) (finU fr cj _) (ratU fr cj (flipForm hT)) := by
  have hnt : Nontrivial (Inf𝔸 F) := (GlobalTheory.InfAdeleCM.ext (Classical.arbitrary (F →+* ℂ))).domain_nontrivial
  constructor
  · rintro γ ⟨γ₀, h⟩
    have h1 : ratTo F (Inf𝔸 F) γ₀ = infU fr cj _ γ := congrArg Prod.fst h
    have h2 : ratTo F (Fin𝔸 F) γ₀ = finU fr cj _ γ := congrArg Prod.snd h
    exact ⟨γ₀, (ratTo_mem fr hT cj hcj (Inf𝔸 F) γ₀).2 hnt (h1 ▸ γ.1.2), h2.symm, h1.symm⟩
  · intro γ₀ h
    exact ⟨(⟨_, (ratTo_mem fr hT cj hcj (Inf𝔸 F) γ₀).1 h⟩, ⟨_, (ratTo_mem fr hT cj hcj (Fin𝔸 F) γ₀).1 h⟩),
      ⟨γ₀, rfl⟩, rfl, rfl⟩

end Adelic

theorem typings_compare [IsTotallyReal F] (cj : E ≃ₐ[F] E) (hcj : ∀ x, cj x = cc x)
    (hF : ∀ x : E, cc x = x → x ∈ Set.range (algebraMap F E))
    (hfg : L0.FG) (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0)
    (hherm : ∀ x y, cc (hT x y) = hT y x) (hnd : (gramOf fr hT).det ≠ 0) (hxi : cc xi0 = -xi0)
    (hsgn : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ xi0).im) (U : Unf Xo c σ r) (hr : n = r)
    (dict : AdelicU F cj fr (flipForm hT) → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup (AdelicU F cj fr (flipForm hT))) :
    let h := flipForm hT
    let 𝔄 : Submodule (𝓞 E) E := AA
    let inf := infU fr cj h
    let fin := finU fr cj h

    (∀ v, finVec F (coord fr v) = toFin F fr v) ∧
    (∀ g, latGHat F fr L0 AA fin g = latAd F fr L0 𝔄 (fin g)) ∧
    (∀ g, latG F fr L0 AA fin g = (GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latG F fr L0 𝔄 (fin g)).map (coord fr).toLinearMap) ∧

    (∀ ι : Dw.La →ₗ[𝓞 E] W, (LatEmb F fr L0 AA fin ((coord fr).toLinearMap ∘ₗ ι) ∧
      LatIsom fr hT xi0 Dw.EF ((coord fr).toLinearMap ∘ₗ ι)) ↔ IsLatEmb h L0 𝔄 xi0 Dw ι) ∧
    (∀ X : Data E r, (ModelW fr hT xi0 hr X ∧ TypeClause H Dw.q X) ↔ IsModelOf H hr fr h xi0 Dw.q X) ∧
    (∀ (X : Data E r) x₀, IsOrthogonalFrame X x₀ ↔ IsOrthoFrame X x₀) ∧
    (∀ ι : Dw.La →ₗ[𝓞 E] W, LinearMap.range ι = latBase L0 𝔄 →
      (KfHalf F fr L0 fin inf.ker Kf l.M (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ↔ IsLevelStab F fr L0 𝔄 l ι inf fin Kf)) ∧

    (∀ (ι : Dw.La →ₗ[𝓞 E] W) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
      (th : (E →+* ℂ) → (Inf𝔸 F ⊗[F] E →+* ℂ)) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
      DictLat F fr L0 AA inf fin (ratU fr cj h) U hr dict ((coord fr).toLinearMap ∘ₗ ι) e Fm ik φ
          (fun _ τ => th τ.1) x₀ ↔
        IsFamilyOf U e Fm ik φ ∧
          IsDictOf F hr fr h L0 𝔄 l ι U.X (fun k a => φ k (Fm.t (ik k) a)) th x₀ inf fin dict) ∧

    (AdPinU F cj hr fr h L0 𝔄 xi0 U dict Kf ↔ ∃ x₀ ι₀, SidePins fr hT L0 xi0 fin inf.ker U hr Kf x₀ ∧
      AdPinWith F fr hT L0 AA xi0 inf fin (ratU fr cj h) U dict x₀ ι₀ fun k mk => IsMarkStab l (U.X k) mk ∧
        ∃ gk, LatMark F hr fr L0 𝔄 l (embW fr hr ι₀) (U.X k) mk (fin gk)) ∧
    (AdPinU F cj hr fr h L0 𝔄 xi0 U dict Kf → ∃ x₀ ι₀, SidePins fr hT L0 xi0 fin inf.ker U hr Kf x₀ ∧
      AdPin F fr hT L0 AA xi0 inf fin (ratU fr cj h) U dict x₀ ι₀) ∧
    ((∀ k, ∃ g, (dict g).1 = k) →
      (AdPinU F cj hr fr h L0 𝔄 xi0 U dict Kf ↔ ∃ x₀ ι₀, SidePins fr hT L0 xi0 fin inf.ker U hr Kf x₀ ∧
        AdPinWith F fr hT L0 AA xi0 inf fin (ratU fr cj h) U dict x₀ ι₀ fun k mk => IsMarkStab l (U.X k) mk)) := by
  intro h 𝔄 inf fin
  have hU : ∀ g, fin g ∈ unitaryOver F cj fr (flipForm hT) (Fin𝔸 F) := fun g => g.2.2
  have hGf : ∀ k, k ∈ inf.ker ↔ inf k = 1 := fun _ => MonoidHom.mem_ker
  have hQ := isRatPoints_ratU fr hT cj hcj
  have hP : AdPinU F cj hr fr h L0 𝔄 xi0 U dict Kf ↔
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.AdPin F hr fr h L0 𝔄 xi0 U inf fin dict Kf := ⟨fun h => h.2.2, fun h => ⟨hcj, hF, h⟩⟩
  rw [hP]
  exact ⟨finVec_coord fr, latGHat_eq fr L0 AA fin, latG_eq fr L0 AA fin,
    latEmb_iff fr hT L0 AA xi0 fin Dw hfg hsp hherm hxi, fun X => model_iff fr hT xi0 H hr Dw.q X hsgn, orthogonal_frame_iff,
    fun ι hι => level_iff fr hT L0 AA inf fin _ l hfg hsp hA hnd cj hU hGf ι hι Kf,
    fun ι _ e Fm ik φ th x₀ => dictLat_iff fr hT L0 AA inf fin _ hQ U hr dict ι e Fm ik φ th x₀,
    joint_iff fr hT L0 AA xi0 inf fin _ _ cj hfg hsp hA hherm hnd hxi hsgn hU hGf hQ U hr dict Kf,
    first_of_second fr hT L0 AA xi0 inf fin _ _ cj hfg hsp hA hherm hnd hxi hsgn hU hGf hQ U hr dict Kf,
    joint_iff_of_onto fr hT L0 AA xi0 inf fin _ _ cj hfg hsp hA hherm hnd hxi hsgn hU hGf hQ U hr dict Kf⟩

theorem xi_hyp (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (h0 : 0 < H.rt0.im) (N : ℕ) (hN : 0 < N)
    (hbar : cc (H.rt : E) = -(H.rt : E)) :
    cc (-1 / ((N : E) * H.rt)) = -(-1 / ((N : E) * H.rt)) ∧
      ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ (-1 / ((N : E) * H.rt))).im := by
  constructor
  · unfold cc at hbar ⊢
    rw [map_div₀, map_mul, hbar, map_neg, map_one, map_natCast, mul_neg, div_neg]
  · intro τ hτ
    rw [map_div₀, map_mul, hτ, map_neg, map_one, map_natCast, neg_div, one_div, Complex.neg_im, Complex.inv_im, neg_div,
      neg_neg]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : 0 < ((N : ℂ) * H.rt0).im := by simpa using mul_pos hN' h0
    exact div_pos h1 (Complex.normSq_pos.2 fun h => by rw [h] at h1; simp at h1)

end Compare

end GlobalTheory.DictPinCompare
