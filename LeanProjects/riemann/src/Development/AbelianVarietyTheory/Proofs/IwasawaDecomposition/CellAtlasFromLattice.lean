import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierIndependentSpanIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellSpanPreserved
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellCoordinatesExist

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan le_preimage_comp)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.CellAtlas

section Lin

variable {R N N' : Type} [CommRing R] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] {m k : ℕ}

theorem initSpan_castLE (hk : k ≤ m) (u : Fin m → N) :
    initSpan R u k = Submodule.span R (Set.range fun i : Fin k => u (Fin.castLE hk i)) := by
  rw [initSpan]
  congr 1
  ext v
  exact ⟨fun ⟨j, hj, e⟩ => ⟨⟨j, hj⟩, e⟩, fun ⟨i, e⟩ => ⟨_, i.2, e⟩⟩

theorem initSpan_top (u : Fin m → N) : initSpan R u m = Submodule.span R (Set.range u) := initSpan_castLE le_rfl u

theorem initSpan_zero (u : Fin m → N) : initSpan R u 0 = ⊥ := by
  simp [initSpan]

theorem map_initSpan (F : N →ₗ[R] N') (u : Fin m → N) (e : ℕ) :
    (initSpan R u e).map F = initSpan R (fun i => F (u i)) e := by
  rw [initSpan, initSpan, Submodule.map_span, Set.image_image]

theorem smooth_C (σ : Type) [Finite σ] : Smooth (spMap (MvPolynomial.C : R →+* MvPolynomial σ R)) := by
  refine (HasRingHomProperty.Spec_iff (P := @Smooth)).2 ?_
  exact RingHom.smooth_algebraMap.2 (⟨inferInstance, inferInstance⟩ : Algebra.Smooth R (MvPolynomial σ R))

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}
  {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}
  {A : Atlas M π ty} {D : LCrd M π} {σ : E →+* ℂ} {a k b : ℕ} {K : Type} [Field K]

theorem bc_bc {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) (u : Vecs Dw M.t R) :
    (u.bc φ).bc ψ = u.bc (ψ.comp φ) := by
  funext τ i
  rw [Vecs.bc, Vecs.bc, Vecs.bc, FlagMod.dualMap_comp, ← spMap_comp', Category.assoc]

theorem linearIndependent_of_flagAt {z : Sp K ⟶ X} {u : TVecs Dw M.t (z ≫ π)} (hu : A.FlagAt z (up u)) (τ : E →+* ℂ) :
    LinearIndependent K (u τ) := by
  obtain ⟨a, φ, -, hf, -⟩ := hu
  exact ((isFrame_up_iff _ _).1 hf τ).1

theorem range_subset_of_flagAt {z : Sp K ⟶ X} {u : Vecs Dw M.t K} (hu : A.FlagAt z u) :
    Set.range z ⊆ π ⁻¹' Set.range M.j := by
  obtain ⟨a, φ, e, -⟩ := hu
  rw [← A.cover]
  exact A.ch.range_subset e

theorem exists_chart {Z : Scheme.{0}} (C : Coc Z) (z : Sp K ⟶ Z) : ∃ β, ⊤ ≤ z ⁻¹ᵁ C.B β :=
  FlagMod.exists_chart_of_isLocalRing (eq_top_iff.2 fun x _ => by
    obtain ⟨β, hβ⟩ := C.cover x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨β, hβ⟩) z

variable (D) in

def embL (α : D.C.A) {S : Type} [CommRing S] (z : Sp S ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) :
    TanM (z ≫ π) M.t.G →ₗ[S] (Fin (D.N + 1) → S) :=
  ((D.Em.A α).map (ev z _ h)).mulVecLin.comp (D.crd α S z h)

theorem embL_injective (α : D.C.A) {z : Sp K ⟶ X} (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (hz : Set.range z ⊆ π ⁻¹' Set.range M.j) :
    Function.Injective (embL D α z h) := by
  obtain ⟨A', hA⟩ := D.Em.linv α
  have h1 : A'.map (ev z _ h) * (D.Em.A α).map (ev z _ h) = 1 := by
    rw [← Matrix.map_mul, hA, Matrix.map_one _ (map_zero _) (map_one _)]
  intro v v' e
  refine D.inj α K z h hz ?_
  have := congrArg (A'.map (ev z _ h)).mulVec e
  simpa only [embL, LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this

theorem emb_congr (α : D.C.A) {z z' : Sp K ⟶ X} (e : z = z') (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (h' : ⊤ ≤ z' ⁻¹ᵁ D.C.B α)
    {U : TVecs Dw M.t (z ≫ π)} {U' : TVecs Dw M.t (z' ≫ π)} (hU : up U = up U') (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    D.emb α z h (U τ i) = D.emb α z' h' (U' τ i) := by
  subst e
  rw [up_injective hU]

variable (D A) in

def Good (hk : k ≤ Dw.mult σ) {X' : Scheme.{0}} (f : X' ⟶ X) (q : X' ⟶ PSpace V (plN D.N k)) (w : Sp K ⟶ X')
    (u : TVecs Dw M.t ((w ≫ f) ≫ π)) : Prop :=
  A.FlagAt (w ≫ f) (up u) ∧
    ∀ α h, Car D.Em f q w α h fun i => D.crd α K (w ≫ f) h (u σ (Fin.castLE hk i))

variable {hk : k ≤ Dw.mult σ} {X' : Scheme.{0}} {f : X' ⟶ X} {q : X' ⟶ PSpace V (plN D.N k)} {w : Sp K ⟶ X'}
  {u u' : TVecs Dw M.t ((w ≫ f) ≫ π)} {ty' : (E →+* ℂ) → Finset ℕ}

theorem good_of_one (hu : A.FlagAt (w ≫ f) (up u)) {α : D.C.A} {h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ D.C.B α}
    (hc : Car D.Em f q w α h fun i => D.crd α K (w ≫ f) h (u σ (Fin.castLE hk i))) : Good A D hk f q w u :=
  ⟨hu, fun β hβ => by
    have := (car_span _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc).2.2 β hβ
    simpa only [D.tr] using this⟩

theorem Good.initSpan_eq (h : Good A D hk f q w u) (h' : Good A D hk f q w u') :
    initSpan K (u' σ) k = initSpan K (u σ) k := by
  obtain ⟨α, hα⟩ := exists_chart D.C (w ≫ f)
  have h1 := (((car_span _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.2 α hα)).2.1 _).1 (h'.2 α hα)).2
  refine Submodule.map_injective_of_injective (D.inj α K _ hα (range_subset_of_flagAt h.1)) ?_
  rw [map_initSpan, map_initSpan, initSpan_castLE hk, initSpan_castLE hk]
  exact h1

theorem Good.of_initSpan_eq (h : Good A D hk f q w u) (hu : A.FlagAt (w ≫ f) (up u'))
    (e : initSpan K (u' σ) k = initSpan K (u σ) k) : Good A D hk f q w u' := by
  refine ⟨hu, fun α hα => ((car_span _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.2 α hα)).2.1 _).2 ⟨?_, ?_⟩⟩
  · exact ((linearIndependent_of_flagAt hu σ).comp _ (Fin.castLE_injective hk)).map' _
      (LinearMap.ker_eq_bot.2 (D.inj α K _ hα (range_subset_of_flagAt hu)))
  · have := congrArg (Submodule.map (D.crd α K (w ≫ f) hα)) e
    rwa [map_initSpan, map_initSpan, initSpan_castLE hk, initSpan_castLE hk] at this

theorem Good.le (h : Good A D hk f q w u) (h' : Good A D hk f q w u') (h1 : ty' σ = insert k (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') : ∀ τ, ∀ j ∈ ty' τ, initSpan K (u' τ) j ≤ initSpan K (u τ) j := by
  intro τ j hj
  by_cases hτ : τ = σ
  swap
  · exact (h'.1.initSpan_eq h.1 τ (h2 τ hτ ▸ hj)).le
  subst hτ
  rw [h1, Finset.mem_insert] at hj
  rcases hj with rfl | hj
  · exact (h.initSpan_eq h').le
  · exact (h'.1.initSpan_eq h.1 τ hj).le

theorem Good.of_le (h : Good A D hk f q w u) {j : A.ch.ι} {φ : A.ch.R j →+* K} (e : spMap φ ≫ A.ch.χ j = w ≫ f)
    (hf : LocM.IsFrame M.t (φ.comp (A.alg j)) ((w ≫ f) ≫ π) (up u')) (h1 : ty' σ = insert k (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') (hle : ∀ τ, ∀ j ∈ ty' τ, initSpan K (u' τ) j ≤ initSpan K (u τ) j) :
    Good A D hk f q w u' := by
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  have hsub : ∀ τ, ∀ j ∈ ty τ, j ∈ ty' τ := fun τ j hj => by
    by_cases hτ : τ = σ
    · subst hτ
      rw [h1]
      exact Finset.mem_insert_of_mem hj
    · rwa [h2 τ hτ]
  have hi := linearIndependent_of_flagAt h.1
  have hF : A.FlagAt (w ≫ f) (up u') := (A.flagAt_iff e h₀ u').2 ⟨hf, fun τ j hj =>
    (initSpan_eq_of_le (hi τ) ((isFrame_up_iff _ _).1 hf τ).1 (hle τ j (hsub τ j hj))).trans
      (((A.flagAt_iff e h₀ u).1 h.1).2 τ j hj)⟩
  exact h.of_initSpan_eq hF (initSpan_eq_of_le (hi σ) ((isFrame_up_iff _ _).1 hf σ).1
    (hle σ k (h1 ▸ Finset.mem_insert_self _ _)))

theorem Good.comp_eq (ho : q ≫ PSpace.str V _ = f ≫ π ≫ M.s) (h : Good A D hk f q w u) {w' : Sp K ⟶ X'}
    {U' : TVecs Dw M.t ((w' ≫ f) ≫ π)} (h' : Good A D hk f q w' U') (e : w ≫ f = w' ≫ f) (hU : up u = up U') :
    w ≫ q = w' ≫ q := by
  obtain ⟨α, hα⟩ := exists_chart D.C (w ≫ f)
  have hα' : ⊤ ≤ (w' ≫ f) ⁻¹ᵁ D.C.B α := e ▸ hα
  obtain ⟨g, hv, h1⟩ := h.2 α hα
  obtain ⟨g', hv', h1'⟩ := h'.2 α hα'
  have hg : g = g' := by
    have h3 : spMap g = spMap g' := by
      rw [← ProjSpace.pt_str g _ hv, ← ProjSpace.pt_str g' _ hv', ← h1, ← h1', Category.assoc, Category.assoc, ho,
        ← Category.assoc, e, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)
  subst hg
  rw [h1, h1']
  congr 2
  funext i
  exact emb_congr α e hα hα' hU σ _

open Classical in

def chg {S : Type} [CommRing S] (p : GPm (Dw.mult σ) a b) (x : GVar (Dw.mult σ) a k b → S)
    {z : Sp S ⟶ M.X} (u : TVecs Dw M.t z) : TVecs Dw M.t z := Function.update u σ (gvec (u σ) p x)

theorem chg_self {S : Type} [CommRing S] (p : GPm (Dw.mult σ) a b) (x : GVar (Dw.mult σ) a k b → S)
    {z : Sp S ⟶ M.X} (u : TVecs Dw M.t z) : chg p x u σ = gvec (u σ) p x := by
  classical
  unfold chg
  convert Function.update_self σ _ u

theorem chg_ne {S : Type} [CommRing S] (p : GPm (Dw.mult σ) a b) (x : GVar (Dw.mult σ) a k b → S)
    {z : Sp S ⟶ M.X} (u : TVecs Dw M.t z) {τ : E →+* ℂ} (h : τ ≠ σ) : chg p x u τ = u τ := by
  classical
  unfold chg
  convert Function.update_of_ne h _ u

theorem isFrame_chg (ha : a ≤ k) (hb : k ≤ b) {S : Type} [CommRing S] (p : GPm (Dw.mult σ) a b)
    (x : GVar (Dw.mult σ) a k b → S) {z : Sp S ⟶ M.X} {u : TVecs Dw M.t z} {g : c.F →+* S}
    (hu : LocM.IsFrame M.t g z (up u)) : LocM.IsFrame M.t g z (up (chg p x u)) := by
  rw [isFrame_up_iff] at hu ⊢
  intro τ
  by_cases hτ : τ = σ
  · subst hτ
    obtain ⟨h1, h2, -⟩ := gvec_frame S _ a k b _ (u τ) p x ha hb
    rw [chg_self, h2]
    exact ⟨h1 (hu τ).1, (hu τ).2⟩
  · rw [chg_ne p x u hτ]
    exact hu τ

theorem tanPull_chg {S S' : Type} [CommRing S] [CommRing S'] (p : GPm (Dw.mult σ) a b)
    (x : GVar (Dw.mult σ) a k b → S) (φ : S →+* S') {z : Sp S ⟶ M.X} {z' : Sp S' ⟶ M.X}
    (e : spMap φ ≫ z = z') (u : TVecs Dw M.t z) :
    (fun τ i => tanPull φ e (chg p x u τ i)) = chg p (φ ∘ x) (fun τ i => tanPull φ e (u τ i)) := by
  funext τ i
  by_cases hτ : τ = σ
  · subst hτ
    rw [chg_self, chg_self, map_gvec]
  · rw [chg_ne _ _ _ hτ, chg_ne _ _ _ hτ]

theorem flagAt_chg (ha : a ≤ k) (hb : k ≤ b) (hty : ∀ e ∈ ty σ, e ≤ a ∨ b ≤ e) (p : GPm (Dw.mult σ) a b)
    (x : GVar (Dw.mult σ) a k b → K) {z : Sp K ⟶ X} {u : TVecs Dw M.t (z ≫ π)}
    (hu : A.FlagAt z (up u)) : A.FlagAt z (up (chg p x u)) := by
  obtain ⟨j, φ, e, -⟩ := id hu
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  obtain ⟨h1, h2⟩ := (A.flagAt_iff e h₀ u).1 hu
  refine (A.flagAt_iff e h₀ _).2 ⟨isFrame_chg ha hb p x h1, fun τ j hj' => Eq.trans ?_ (h2 τ j hj')⟩
  by_cases hτ : τ = σ
  · subst hτ
    rw [chg_self, (gvec_frame K _ a k b _ (u τ) p x ha hb).2.2 _ (hty j hj')]
  · rw [chg_ne _ _ _ hτ]

theorem embL_gvec {α : A.ch.ι → D.C.A} {cv : ∀ j, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R j}
    (hS : IsFrVec D A σ α cv) {j : A.ch.ι} {φ : A.ch.R j →+* K} {z : Sp K ⟶ X} (e : spMap φ ≫ A.ch.χ j = z)
    (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (α j)) {u : TVecs Dw M.t (z ≫ π)} (hu : up u = (A.fr j).bc φ) (p : GPm (Dw.mult σ) a b)
    (x : GVar (Dw.mult σ) a k b → K) :
    (fun i => embL D (α j) z h (gvec (u σ) p x i)) = gvec (fun i => φ ∘ cv j i) p x := by
  funext i
  rw [map_gvec, funext (hS j K φ z e h u hu)]
  rfl

theorem exists_cell {α : A.ch.ι → D.C.A} {cv Dv : ∀ j, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R j}
    (hk : k ≤ Dw.mult σ) (ha : a ≤ k) (hb : k ≤ b) (ha' : a ∈ ty σ ∨ a = 0) (hb' : b ∈ ty σ ∨ b = Dw.mult σ)
    (hα : ∀ j, ⊤ ≤ A.ch.χ j ⁻¹ᵁ D.C.B (α j)) (hS : IsFrVec D A σ α cv) (hD : ∀ j, LeftInv (Dv j) (cv j))
    {j : A.ch.ι} {φ : A.ch.R j →+* K} {u : Vecs Dw M.t K} (hu : A.FlagAt (spMap φ ≫ A.ch.χ j) u) :
    ∃ (p : GPm (Dw.mult σ) a b) (x : GVar (Dw.mult σ) a k b → K), ∀ z : Sp K ⟶ X, z = spMap φ ≫ A.ch.χ j →
      ∀ U U₀ : TVecs Dw M.t (z ≫ π), up U = u → up U₀ = (A.fr j).bc φ →
        initSpan K (U σ) k = initSpan K (gvec (U₀ σ) p x) k := by
  obtain ⟨U, rfl⟩ := hu.exists_up
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr (φ := φ) rfl
  obtain ⟨h1, h2⟩ := (A.flagAt_iff rfl h₀ U).1 hu
  have h : ⊤ ≤ (spMap φ ≫ A.ch.χ j) ⁻¹ᵁ D.C.B (α j) := le_preimage_comp _ (hα j)
  have hi := embL_injective (α j) h (range_subset_of_flagAt hu)
  set F := embL D (α j) _ h with hF
  have hc : (fun i => φ ∘ cv j i) = fun i => F (u₀ σ i) := funext (hS j K φ _ rfl h u₀ h₀)
  have hs : Submodule.span K (Set.range fun i : Fin k => F (U σ (Fin.castLE hk i))) = (initSpan K (U σ) k).map F := by
    rw [map_initSpan, initSpan_castLE hk]
  have h3 : initSpan K (u₀ σ) a ≤ initSpan K (U σ) k := by
    rcases ha' with h' | rfl
    · rw [← h2 σ a h']
      exact FlagMod.initSpan_mono _ ha
    · rw [initSpan_zero]
      exact bot_le
  have h4 : initSpan K (U σ) k ≤ initSpan K (u₀ σ) b := by
    refine (FlagMod.initSpan_mono _ hb).trans ?_
    rcases hb' with h' | rfl
    · exact (h2 σ b h').le
    · have f₀ := A.isFrame_bc (φ := φ) rfl
      rw [← h₀] at f₀
      rw [initSpan_top, initSpan_top, ((isFrame_up_iff _ _).1 f₀ σ).2, ((isFrame_up_iff _ _).1 h1 σ).2]
  obtain ⟨⟨p, hp⟩, h5⟩ := Normal.main K _ a k b _ hk (fun i => φ ∘ Dv j i) (fun i => φ ∘ cv j i)
    (fun i => F (U σ (Fin.castLE hk i))) ha hb ((hD j).map φ)
    (((linearIndependent_of_flagAt hu σ).comp _ (Fin.castLE_injective hk)).map' _ (LinearMap.ker_eq_bot.2 hi))
    (by rw [hs, hc, ← map_initSpan]; exact Submodule.map_mono h3)
    (by rw [hs, hc, ← map_initSpan]; exact Submodule.map_mono h4)
  obtain ⟨x, hx⟩ := h5 p hp
  refine ⟨p, x, ?_⟩
  rintro z rfl U' U₀ hU' hU₀
  rw [up_injective hU', up_injective (hU₀.trans h₀.symm)]
  refine Submodule.map_injective_of_injective hi ?_
  rw [← hs, hx, map_initSpan, embL_gvec hS rfl h h₀]

section Closure

variable {α : A.ch.ι → D.C.A} {cv Dv : ∀ j, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R j}
  {κ : ∀ j : A.ch.ι, GPm (Dw.mult σ) a b → (Sp (MvPolynomial (GVar (Dw.mult σ) a k b) (A.ch.R j)) ⟶ X')}
  (cl : CellCl (π ≫ M.s) A.ch (fun j => (A.alg j).comp V.subtype) (fun j => gxi a b hk (cv j)) f q κ)

def frBelow (j : A.ch.ι) (p : GPm (Dw.mult σ) a b) : TVecs Dw M.t ((κ j p ≫ f) ≫ π) :=
  (A.exists_up_fr (cl.sq j p).symm).choose

theorem up_frBelow (j : A.ch.ι) (p : GPm (Dw.mult σ) a b) : up (frBelow cl j p) = (A.fr j).bc MvPolynomial.C :=
  (A.exists_up_fr (cl.sq j p).symm).choose_spec

def charts : Charts X' where
  ι := A.ch.ι × GPm (Dw.mult σ) a b
  R i := MvPolynomial (GVar (Dw.mult σ) a k b) (A.ch.R i.1)
  χ i := κ i.1 i.2
  opn i := cl.opn i.1 i.2

def pre : PreAtlas M X' where
  ch := charts cl
  alg i := (MvPolynomial.C : A.ch.R i.1 →+* MvPolynomial (GVar (Dw.mult σ) a k b) (A.ch.R i.1)).comp (A.alg i.1)
  fr i := up (chg i.2 MvPolynomial.X (frBelow cl i.1 i.2))

theorem carrier_eq : (charts cl).carrier = f ⁻¹' A.ch.carrier := by
  rw [← cl.cover, Charts.carrier]
  exact Set.iUnion_prod' fun i : A.ch.ι × GPm (Dw.mult σ) a b => Set.range (κ i.1 i.2)

include cl in
theorem sq_point (j : A.ch.ι) (p : GPm (Dw.mult σ) a b)
    {ψ : MvPolynomial (GVar (Dw.mult σ) a k b) (A.ch.R j) →+* K} {w : Sp K ⟶ X'} (e : spMap ψ ≫ κ j p = w) :
    spMap (ψ.comp MvPolynomial.C) ≫ A.ch.χ j = w ≫ f := by
  rw [← spMap_comp', Category.assoc, ← cl.sq, ← Category.assoc, e]

theorem exists_good (ha : a ≤ k) (hb : k ≤ b) (hty : ∀ e ∈ ty σ, e ≤ a ∨ b ≤ e)
    (hα : ∀ j, ⊤ ≤ A.ch.χ j ⁻¹ᵁ D.C.B (α j)) (hS : IsFrVec D A σ α cv) (j : A.ch.ι) (p : GPm (Dw.mult σ) a b)
    {ψ : MvPolynomial (GVar (Dw.mult σ) a k b) (A.ch.R j) →+* K} {w : Sp K ⟶ X'} (e : spMap ψ ≫ κ j p = w) :
    ∃ U₀ : TVecs Dw M.t ((w ≫ f) ≫ π), up U₀ = (A.fr j).bc (ψ.comp MvPolynomial.C) ∧
      up (chg p (ψ ∘ MvPolynomial.X) U₀) = ((pre cl).fr (j, p)).bc ψ ∧
      Good A D hk f q w (chg p (ψ ∘ MvPolynomial.X) U₀) := by
  have e' := sq_point cl j p e
  have e2 : spMap ψ ≫ (κ j p ≫ f) ≫ π = (w ≫ f) ≫ π := by
    rw [← e]; simp only [Category.assoc]
  let U₀ : TVecs Dw M.t ((w ≫ f) ≫ π) := fun τ i => tanPull ψ e2 (frBelow cl j p τ i)
  have h₀ : up U₀ = (A.fr j).bc (ψ.comp MvPolynomial.C) := by
    rw [up_tanPull ψ e2, up_frBelow, bc_bc]
  have hF : A.FlagAt (w ≫ f) (up U₀) := h₀ ▸ A.flagAt_fr e'
  have hU : (fun τ i => tanPull ψ e2 (chg p MvPolynomial.X (frBelow cl j p) τ i)) = chg p (ψ ∘ MvPolynomial.X) U₀ :=
    tanPull_chg p _ ψ e2 _
  refine ⟨U₀, h₀, ?_, ?_⟩
  · rw [← hU]
    exact up_tanPull ψ e2 _
  · have h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ D.C.B (α j) := e' ▸ le_preimage_comp _ (hα _)
    refine good_of_one (flagAt_chg ha hb hty p _ hF) (α := α j) (h := h) ?_
    obtain ⟨hv, h1⟩ := cl.pl j p
    have h2 : ψ ∘ gxi a b hk (cv j) p = plk (fun i => ((D.Em.A (α j)).map (ev (w ≫ f) _ h)).mulVec
        (D.crd (α j) K (w ≫ f) h (chg p (ψ ∘ MvPolynomial.X) U₀ σ (Fin.castLE hk i)))) id := by
      rw [gxi, FlagEmb.map_plk, chg_self]
      have h3 := embL_gvec hS e' h h₀ p (ψ ∘ MvPolynomial.X)
      have h4 : (fun z => ψ ∘ gvec (fun i => (MvPolynomial.C : A.ch.R j →+* MvPolynomial (GVar (Dw.mult σ) a k b) _) ∘ cv j i)
          p (MvPolynomial.X : GVar (Dw.mult σ) a k b → MvPolynomial (GVar (Dw.mult σ) a k b) (A.ch.R j)) z) = fun i => embL D (α j) (w ≫ f) h (gvec (U₀ σ) p (ψ ∘ MvPolynomial.X) i) := by
        rw [h3]
        funext z
        exact comp_gvec ψ _ p _ z
      rw [h4]
      rfl
    refine ⟨ψ.comp (MvPolynomial.C.comp ((A.alg j).comp V.subtype)), h2 ▸ ProjSpace.span_range_comp_eq_top _ hv ψ, ?_⟩
    have h5 : w ≫ q = spMap ψ ≫ κ j p ≫ q := by rw [← Category.assoc, e]
    rw [h5, h1, ProjSpace.spMap_pt]
    congr 1

theorem pre_flagAt_iff (ha : a ≤ k) (hb : k ≤ b) (hty : ∀ e ∈ ty σ, e ≤ a ∨ b ≤ e)
    (hα : ∀ j, ⊤ ≤ A.ch.χ j ⁻¹ᵁ D.C.B (α j)) (hS : IsFrVec D A σ α cv) (h1 : ty' σ = insert k (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') (w : Sp K ⟶ X') (U : TVecs Dw M.t ((w ≫ f) ≫ π)) :
    (pre cl).FlagAt (f ≫ π) ty' w (up U) ↔ Good A D hk f q w U := by
  have ex : w ≫ f ≫ π = (w ≫ f) ≫ π := (Category.assoc _ _ _).symm
  constructor
  · rintro ⟨⟨j, p⟩, ψ, e, hf, hs⟩
    obtain ⟨U₀, -, hU₀, hg⟩ := exists_good cl ha hb hty hα hS j p e
    rw [ex] at hf hs
    refine hg.of_le (sq_point cl j p e) hf h1 h2 ((sameFlag_up_iff _ _).1 ?_)
    rw [hU₀]
    exact hs
  · intro hg
    obtain ⟨j₀, φ, e, -⟩ := id hg.1
    have hr : w (IsLocalRing.closedPoint K) ∈ (charts cl).carrier := by
      rw [carrier_eq]
      exact A.ch.range_subset e ⟨IsLocalRing.closedPoint K, rfl⟩
    obtain ⟨⟨j, p⟩, ψ, eq⟩ := (charts cl).exists_fac w hr
    obtain ⟨U₀, h₀, hU₀, hg₀⟩ := exists_good cl ha hb hty hα hS j p eq
    have hfr := ((A.flagAt_iff (sq_point cl j p eq) h₀ U).1 hg.1).1
    have hs := (sameFlag_up_iff _ U).2 (hg₀.le hg h1 h2)
    rw [hU₀] at hs
    exact ⟨(j, p), ψ, eq, by rw [ex]; exact hfr, by rw [ex]; exact hs⟩

theorem pre_cover : (charts cl).carrier = (f ≫ π) ⁻¹' Set.range M.j := by
  rw [carrier_eq, A.cover]
  ext x
  simp only [Set.mem_preimage, Scheme.Hom.comp_apply]

include cl in
theorem pre_alg_s (j : A.ch.ι) (p : GPm (Dw.mult σ) a b) : κ j p ≫ (f ≫ π) ≫ M.s =
    spMap (((MvPolynomial.C : A.ch.R j →+* MvPolynomial (GVar (Dw.mult σ) a k b) _).comp (A.alg j)).comp V.subtype) := by
  have := A.affineOpenChart_comp_structure_eq_spMap (cl.sq j p).symm
  simp only [Category.assoc] at this ⊢
  exact this

include cl in
theorem pre_smooth (j : A.ch.ι) (p : GPm (Dw.mult σ) a b) : Smooth (κ j p ≫ f ≫ π) := by
  have h3 : κ j p ≫ f ≫ π = spMap MvPolynomial.C ≫ A.ch.χ j ≫ π := by
    rw [← Category.assoc, cl.sq, Category.assoc]
  have := smooth_C (R := A.ch.R j) (GVar (Dw.mult σ) a k b)
  have := A.smooth j
  rw [h3]
  infer_instance

theorem pre_frame (ha : a ≤ k) (hb : k ≤ b) (j : A.ch.ι) (p : GPm (Dw.mult σ) a b) :
    LocM.IsFrame M.t ((MvPolynomial.C : A.ch.R j →+* MvPolynomial (GVar (Dw.mult σ) a k b) _).comp (A.alg j))
      (κ j p ≫ f ≫ π) (up (chg p MvPolynomial.X (frBelow cl j p))) := by
  have hf := A.isFrame_bc (cl.sq j p).symm
  rw [← up_frBelow cl] at hf
  have h5 : ∀ {S : Type} [CommRing S] {g : c.F →+* S} {x x' : Sp S ⟶ M.X} (_ : x = x') {v : Vecs Dw M.t S},
      LocM.IsFrame M.t g x v → LocM.IsFrame M.t g x' v := by
    rintro _ _ _ _ _ rfl _ h
    exact h
  exact h5 (Category.assoc _ _ _) (isFrame_chg ha hb p _ hf)

theorem pre_glue (ha : a ≤ k) (hb : k ≤ b) (hty : ∀ e ∈ ty σ, e ≤ a ∨ b ≤ e)
    (hα : ∀ j, ⊤ ≤ A.ch.χ j ⁻¹ᵁ D.C.B (α j)) (hS : IsFrVec D A σ α cv) (h1 : ty' σ = insert k (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') (K : Type) [Field K] (j j' : A.ch.ι) (p p' : GPm (Dw.mult σ) a b)
    (ψ : MvPolynomial (GVar (Dw.mult σ) a k b) (A.ch.R j) →+* K)
    (ψ' : MvPolynomial (GVar (Dw.mult σ) a k b) (A.ch.R j') →+* K) (e : spMap ψ ≫ κ j p = spMap ψ' ≫ κ j' p') :
    SameFlag ty' M.t (spMap ψ ≫ κ j p ≫ f ≫ π) (((pre cl).fr (j, p)).bc ψ) (((pre cl).fr (j', p')).bc ψ') := by
  obtain ⟨U, -, hU, hg⟩ := exists_good cl ha hb hty hα hS j p (rfl : spMap ψ ≫ κ j p = _)
  obtain ⟨U', -, hU', hg'⟩ := exists_good cl ha hb hty hα hS j' p' e.symm
  have hs := (sameFlag_up_iff _ _).2 (hg.le hg' h1 h2)
  rw [hU, hU'] at hs
  have ex : spMap ψ ≫ κ j p ≫ f ≫ π = ((spMap ψ ≫ κ j p) ≫ f) ≫ π := by
    simp only [Category.assoc]
  rw [ex]
  exact hs

def atlas (ha : a ≤ k) (hb : k ≤ b) (ha' : a ∈ ty σ ∨ a = 0) (hb' : b ∈ ty σ ∨ b = Dw.mult σ)
    (hty : ∀ e ∈ ty σ, e ≤ a ∨ b ≤ e) (hα : ∀ j, ⊤ ≤ A.ch.χ j ⁻¹ᵁ D.C.B (α j)) (hS : IsFrVec D A σ α cv)
    (hD : ∀ j, LeftInv (Dv j) (cv j)) (h1 : ty' σ = insert k (ty σ)) (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') :
    Atlas M (f ≫ π) ty' where
  toPreAtlas := pre cl
  cover := pre_cover cl
  alg_s i := pre_alg_s cl i.1 i.2
  smooth i := pre_smooth cl i.1 i.2
  frame i := pre_frame cl ha hb i.1 i.2
  glue K _ i i' ψ ψ' e := pre_glue cl ha hb hty hα hS h1 h2 K i.1 i'.1 i.2 i'.2 ψ ψ' e
  bij K _ g y hy u hu := by
    obtain ⟨w₀, ⟨hw₀, hF⟩, hun⟩ := A.bij K g y hy u hu
    obtain ⟨j, φ, rfl, -⟩ := id hF
    obtain ⟨p, x, hpx⟩ := exists_cell hk ha hb ha' hb' hα hS hD hF
    have hx : ∀ {w' : Sp K ⟶ X'}, w' ≫ f ≫ π = y ≫ M.j → ∃ U : TVecs Dw M.t ((w' ≫ f) ≫ π), up U = u :=
      fun {w'} e => exists_up fun τ i => by
        have e' : (w' ≫ f) ≫ π = y ≫ M.j := (Category.assoc _ _ _).trans e
        rw [e']
        exact (hu.1 τ i).1
    obtain ⟨w, e⟩ : ∃ w, spMap (MvPolynomial.eval₂Hom φ x) ≫ κ j p = w := ⟨_, rfl⟩
    have hC : (MvPolynomial.eval₂Hom φ x).comp MvPolynomial.C = φ := MvPolynomial.eval₂Hom_comp_C φ x
    have hX : MvPolynomial.eval₂Hom φ x ∘ MvPolynomial.X = x := funext fun i => MvPolynomial.eval₂Hom_X' φ x i
    have hw1 : w ≫ f = spMap φ ≫ A.ch.χ j := by rw [← sq_point cl j p e, hC]
    have hw : w ≫ f ≫ π = y ≫ M.j := by rw [← Category.assoc, hw1, hw₀]
    have h3 : A.FlagAt (w ≫ f) u := by rw [hw1]; exact hF
    obtain ⟨U, rfl⟩ := hx hw
    obtain ⟨U₀, h₀, -, hg₀⟩ := exists_good cl ha hb hty hα hS j p e
    rw [hC] at h₀
    rw [hX] at hg₀
    have hg : Good A D hk f q w U := hg₀.of_initSpan_eq h3 (by rw [chg_self]; exact hpx _ hw1 U U₀ rfl h₀)
    refine ⟨w, ⟨hw, (pre_flagAt_iff cl ha hb hty hα hS h1 h2 w U).2 hg⟩, ?_⟩
    rintro w' ⟨e1, e2⟩
    obtain ⟨U', hU'⟩ := hx e1
    rw [← hU'] at e2
    have hg' := (pre_flagAt_iff cl ha hb hty hα hS h1 h2 w' U').1 e2
    have e3 : w ≫ f = w' ≫ f := hw1.trans (hun _ ⟨(Category.assoc _ _ _).trans e1, hU' ▸ hg'.1⟩).symm
    exact (cl.inj K w w' (A.ch.range_subset hw1.symm) e3 (hg.comp_eq cl.ovr hg' e3 hU'.symm)).symm

end Closure

theorem exists_cellAtlas (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype)
    (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (D : LCrd M π) (σ : E →+* ℂ)
    (α : A.ch.ι → D.C.A) (cv Dv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a) (a k b : ℕ) (hk : k ≤ Dw.mult σ)
    (X' : Scheme.{0}) (f : X' ⟶ X) (q : X' ⟶ PSpace V (plN D.N k))
    (κ : ∀ j : A.ch.ι, GPm (Dw.mult σ) a b → (Sp (MvPolynomial (GVar (Dw.mult σ) a k b) (A.ch.R j)) ⟶ X'))
    (ty' : (E →+* ℂ) → Finset ℕ) : a ≤ k → k ≤ b → (a ∈ ty σ ∨ a = 0) → (b ∈ ty σ ∨ b = Dw.mult σ) →
      (∀ e ∈ ty σ, e ≤ a ∨ b ≤ e) → (∀ j, ⊤ ≤ A.ch.χ j ⁻¹ᵁ D.C.B (α j)) → IsFrVec D A σ α cv →
      (∀ j, LeftInv (Dv j) (cv j)) →
      CellCl (π ≫ M.s) A.ch (fun j => (A.alg j).comp V.subtype) (fun j => gxi a b hk (cv j)) f q κ →
      ty' σ = insert k (ty σ) → (∀ σ', σ' ≠ σ → ty' σ' = ty σ') →
      ∃ A' : Atlas M (f ≫ π) ty', GRel D A σ hk f q A' := fun ha hb ha' hb' hty hα hS hD cl h1 h2 =>
  ⟨atlas cl ha hb ha' hb' hty hα hS hD h1 h2, fun _ _ w U => pre_flagAt_iff cl ha hb hty hα hS h1 h2 w U⟩

end GlobalTheory.GrCl.CellAtlas
