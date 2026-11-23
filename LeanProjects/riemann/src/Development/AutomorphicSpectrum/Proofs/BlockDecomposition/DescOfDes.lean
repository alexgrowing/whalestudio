import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompShiftZero
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
universe w v u t

noncomputable section

namespace GlobalTheory.CompanionTheory.DescTest

section Generic

variable {𝓐 : Type u} [Category.{v} 𝓐] (W : ObjectProperty 𝓐) (P : 𝓐 ⥤ Type t)

def jG : (W.ι ⋙ P).Elements ⥤ P.Elements where
  obj T := ⟨T.1.obj, T.2⟩
  map f := ⟨f.1.hom, f.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def toPts (T : P.Elements) : StructuredArrow T (jG W P) ⥤ (pts W.ι T.1).Elements where
  obj x := ⟨x.right.1, x.hom.1⟩
  map {x x'} f := ⟨f.right.1, congrArg Subtype.val (StructuredArrow.w f)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance (T : P.Elements) : (toPts W P T).Faithful :=
  ⟨fun {x x'} {f g} h => StructuredArrow.hom_ext _ _ (Subtype.ext
    (congrArg (fun z : (toPts W P T).obj x ⟶ (toPts W P T).obj x' => z.1) h))⟩

instance (T : P.Elements) : (toPts W P T).Full :=
  ⟨fun {x x'} g => by
    have hw : x.hom.1 ≫ g.1.hom = x'.hom.1 := g.2
    have a : P.map x.hom.1 T.2 = x.right.2 := x.hom.2
    have a' : P.map x'.hom.1 T.2 = x'.right.2 := x'.hom.2
    have h2 : P.map g.1.hom x.right.2 = x'.right.2 := by
      rw [← a, ← a', ← hw, Functor.map_comp_apply]
      rfl
    refine ⟨StructuredArrow.homMk ⟨g.1, h2⟩ (Subtype.ext hw), rfl⟩⟩

def ptOf (T : P.Elements) (e : (pts W.ι T.1).Elements) : (W.ι ⋙ P).Elements := ⟨e.1, P.map e.2 T.2⟩

instance (T : P.Elements) : (toPts W P T).EssSurj :=
  ⟨fun e => ⟨StructuredArrow.mk (Y := ptOf W P T e) ⟨e.2, rfl⟩, ⟨Iso.refl _⟩⟩⟩

instance (T : P.Elements) : (toPts W P T).IsEquivalence := { }

variable {R : Type} [CommRing R] (Ff : 𝓐 ⥤ ModuleCat.{w} R) (Gf : P.Elements ⥤ ModuleCat.{w} R)
  (θ : ∀ T : P.Elements, Ff.obj T.1 ≃ₗ[R] Gf.obj T)
  (hθ : ∀ {T T' : P.Elements} (f : T ⟶ T') (x : Ff.obj T.1),
    θ T' ((Ff.map f.1).hom x) = (Gf.map f).hom (θ T x))

def mor (T : P.Elements) :
    Mor (elF (pts W.ι T.1) (W.ι ⋙ Ff)) (StructuredArrow.proj T (jG W P) ⋙ jG W P ⋙ Gf) (RingHom.id R) where
  G := toPts W P T
  τ x := (θ ((jG W P).obj x.right)).toLinearMap
  nat {x x'} φ y := hθ ((jG W P).map φ.right) y

include hθ in
theorem mor_aug (T : P.Elements) (y : Ff.obj T.1) :
    (mor W P Ff Gf θ hθ T).hom.f 0 (ptsAug W.ι Ff T.1 y) = unAug Gf (jG W P) T (θ T y) := by
  funext s
  exact (hθ (s.obj (Fin.last 0)).hom y)

theorem res_of_comp {K : Cx.{w} R} {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    (e : M ≃ₗ[R] M') (ε : M' →ₗ[R] K.X 0) (s : R) (h : K.ResUpTo s (ε ∘ₗ e.toLinearMap)) : K.ResUpTo s ε := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, h3⟩
  · simpa using h0 (e.symm x)
  · have := h1 (e.symm x) (by simpa using hx)
    simpa using congrArg e this
  · obtain ⟨x, hx⟩ := h2 y hy
    exact ⟨e x, hx⟩

include hθ in

theorem desc_of_des (s : R) (h : CrystallineSemistableComparison.D.DesJ W.ι Ff s) : Desc s Gf (jG W P) := by
  intro T
  let m := mor W P Ff Gf θ hθ T
  haveI : m.G.IsLeftAdjoint := inferInstanceAs (toPts W P T).IsLeftAdjoint
  have hup : ∀ n, UpTo (1 : R) (m.hom.mapH n) := fun n =>
    ((CrystallineSemistableComparison.P.upTo_alg (m.hom.mapH n) LinearMap.id 1 1).2.2.2.2).2
      (CrystallineSemistableComparison.P.adj_mor m (fun x => (θ ((jG W P).obj x.right)).bijective) n)
  have h1 := (CrystallineSemistableComparison.P.res_transfer m.hom (ptsAug W.ι Ff T.1) s 1 hup).1 (h T.1)
  rw [mul_one] at h1
  refine res_of_comp (θ T) _ s ?_
  have e : m.hom.f 0 ∘ₗ ptsAug W.ι Ff T.1 = unAug Gf (jG W P) T ∘ₗ (θ T).toLinearMap :=
    LinearMap.ext fun y => mor_aug W P Ff Gf θ hθ T y
  rwa [← e]

end Generic

section Steps

variable {𝓐 : Type u} [Category.{v} 𝓐] (W : ObjectProperty 𝓐) (P : 𝓐 ⥤ Type t)
  {b : Base} {L : b.Fun} {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)
  (gG : P.Elements ⥤ Thick L) (Ff : 𝓐 ⥤ ModuleCat.{0} Λ)
  (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ) (hμ : c μ ∈ b.I) (r : ℕ)
  (v : ∀ T : P.Elements, Ff.obj T.1 → (gG.obj T).B)
  (v_add : ∀ T x y, v T (x + y) = v T x + v T y)
  (v_smul : ∀ T (a : Λ) x, v T (a • x) = (gG.obj T).i (c a) * v T x)
  (v_inj : ∀ T, Function.Injective (v T))
  (v_mem : ∀ T (y : (gG.obj T).B), y ∈ (gG.obj T).pdPow (ρ r) ↔ ∃ x, v T x = y)

def stepLin (T : P.Elements) :
    Ff.obj T.1 →ₗ[Λ] (((pdFlt L c ρ hρ μ hμ).comap gG).S r).fn.obj T where
  toFun x := (⟨v T x, (v_mem T _).2 ⟨x, rfl⟩⟩ : (((pdFlt L c ρ hρ μ hμ).comap gG).S r).S T)
  map_add' x y := Subtype.ext (v_add T x y)
  map_smul' a x := Subtype.ext (v_smul T a x)

def stepEquiv (T : P.Elements) :
    Ff.obj T.1 ≃ₗ[Λ] (((pdFlt L c ρ hρ μ hμ).comap gG).S r).fn.obj T :=
  LinearEquiv.ofBijective (stepLin P c gG Ff ρ hρ μ hμ r v v_add v_smul v_mem T)
    ⟨fun x y h => v_inj T (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := (v_mem T _).1 y.2
      exact ⟨x, Subtype.ext hx⟩⟩

include v_add v_smul v_inj v_mem in

theorem desc_step (v_nat : ∀ {T T' : P.Elements} (f : T ⟶ T') (x : Ff.obj T.1),
      v T' ((Ff.map f.1).hom x) = (gG.map f).φ (v T x)) (s : Λ) (h : CrystallineSemistableComparison.D.DesJ W.ι Ff s) :
    Desc s (((pdFlt L c ρ hρ μ hμ).comap gG).S r).fn (jG W P) :=
  desc_of_des W P Ff _ (stepEquiv P c gG Ff ρ hρ μ hμ r v v_add v_smul v_inj v_mem)
    (fun f x => Subtype.ext (v_nat f x)) s h

include hρ in

theorem raise (T : Thick L) (ξ : Λ) (hξ : T.i (c ξ) ∈ T.J) (x : (OM L c).obj T)
    (hx : x ∈ (pdS L c (ρ r)).S T) : ξ • x ∈ (pdS L c (ρ (r + 1))).S T :=
  T.pdPow_anti (hρ.2 r) (mul_pdPow L T _ hξ hx)

include hρ in

theorem desc_flt {C' : Type*} [Category C'] (G : C' ⥤ P.Elements) (μ' ξ : Λ) (hμ' : μ = μ' * ξ)
    (hm : ∀ T : P.Elements, (gG.obj T).i (c ξ) ∈ (gG.obj T).J)
    (h : ∀ r, Desc μ' (((pdFlt L c ρ hρ μ hμ).comap gG).S r).fn G) :
    Desc (Polynomial.X : Polynomial ℤ) (gG ⋙ (pdFlt L c ρ hρ μ hμ).rees) G :=
  GlobalTheory.CompanionTheory.ReesUp.desc_rees ((pdFlt L c ρ hρ μ hμ).comap gG) G μ' ξ hμ'
    (fun r T x hx => raise c ρ hρ r (gG.obj T) ξ (hm T) x hx) h

end Steps

section Concrete
variable {l : ℕ} [Fact l.Prime]

def fv {A : PAlg l} {n m : ℕ} (x : (FilF l n m).obj A) : A.Acr n := (show (FilS l n m).S A from x).1

theorem fv_mem {A : PAlg l} {n m : ℕ} (x : (FilF l n m).obj A) : fv x ∈ A.Fil n m :=
  (Submodule.restrictScalars_mem (Acris l) _ _).1 (show (FilS l n m).S A from x).2

def fmk {A : PAlg l} {n m : ℕ} (y : A.Acr n) (h : y ∈ A.Fil n m) : (FilF l n m).obj A :=
  (⟨y, (Submodule.restrictScalars_mem (Acris l) (A.Fil n m) y).2 h⟩ : (FilS l n m).S A)

theorem fv_inj {A : PAlg l} {n m : ℕ} {x x' : (FilF l n m).obj A} (h : fv x = fv x') : x = x' := Subtype.ext h

theorem fv_add {A : PAlg l} {n m : ℕ} (x x' : (FilF l n m).obj A) : fv (x + x') = fv x + fv x' := rfl

theorem fv_smul {A : PAlg l} {n m : ℕ} (a : Acris l) (x : (FilF l n m).obj A) : fv (a • x) = A.cris n a * fv x := rfl

theorem fv_map {A B : PAlg l} (f : A ⟶ B) {n m : ℕ} (x : (FilF l n m).obj A) :
    fv (((FilF l n m).map f).hom x) = mapAcr f n (fv x) := rfl

end Concrete

section Main

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

theorem fil_eq (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hk : k = false ∨ ρ = 0) (T : (F.pt κ).Elements) (r : ℕ) :
    (gObj F κ k n T).pdPow (ρ r) = T.1.Fil n (ρ r) := by
  have h := (GlobalTheory.CompanionTheory.AcrMod.acr_modp T.1 n).2.2.2.1
  rcases hk with rfl | rfl
  · exact (pdPow_eq_fil _ _ _).trans (h (ρ r))
  · have h0 : (gObj F κ false n T).pdPow 0 = T.1.Fil n 0 := (pdPow_eq_fil _ _ _).trans (h 0)
    rw [Thick.pdPow_zero] at h0
    exact (Thick.pdPow_zero _).trans h0

theorem v_mem (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hk : k = false ∨ ρ = 0) (r : ℕ) (T : (F.pt κ).Elements)
    (y : T.1.Acr n) :
    y ∈ (gObj F κ k n T).pdPow (ρ r) ↔ ∃ x : (FilF l n (ρ r)).obj T.1, fv x = y := by
  rw [fil_eq F κ k n ρ hk T r]
  exact ⟨fun h => ⟨fmk y h, rfl⟩, fun ⟨x, hx⟩ => hx ▸ fv_mem x⟩

theorem xi_mem (k : Bool) (n : ℕ) (T : (F.pt κ).Elements) (ξ : Acris l) (h : T.1.cris n ξ ∈ T.1.Fil n 1) :
    (gObj F κ k n T).i ((base l).cris n ξ) ∈ (gObj F κ k n T).J := by
  have e : (gObj F κ k n T).i ((base l).cris n ξ) = T.1.cris n ξ := mapAcr_cris T.1.fromBase n ξ
  rw [e]
  exact fil_le k T.1 n h

theorem desc_fil (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ) (hk : k = false ∨ ρ = 0) (r : ℕ)
    (s : Acris l) (h : CrystallineSemistableComparison.D.Des (FilF l n (ρ r)) s) :
    Desc s (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).fn (jE (F.pt κ)) :=
  desc_step (fun A : PAlg l => A.IsTest) (F.pt κ) ((base l).cris n) (gE F κ k n) (FilF l n (ρ r)) ρ hρ ε.μ
    (ε.μ_mem k (base l) n) r (fun T x => fv x)
    (fun T x y => fv_add x y)
    (fun T a x => (fv_smul a x).trans (congrArg (· * fv x) (mapAcr_cris T.1.fromBase n a).symm))
    (fun T x y h => fv_inj h)
    (fun T y => v_mem F κ k n ρ hk r T y)
    (fun f x => fv_map f.1 x) s h

end Main

set_option maxHeartbeats 1000000 in
theorem des_qk {l : ℕ} [Fact l.Prime] (hOut : D.Out l) (ε : Eps l)
    (h1 : D.InWm l (WittVector.teichmuller l (ε.e 1 : Ob l) - 1)) (n m : ℕ) :
    CrystallineSemistableComparison.D.Des (FilF l n m) (ε.qk 1 - 1) := by
  have hs : algebraMap (Ainf l) (Acris l) (WittVector.teichmuller l (ε.e 1 : Ob l) - 1) = ε.qk 1 - 1 := by
    rw [map_sub, map_one, Eps.qk]
  rw [← hs]
  exact (hOut _ h1 n).2.2 m

end GlobalTheory.CompanionTheory.DescTest
