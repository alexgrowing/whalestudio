import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BalancedLiftTmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonTensor
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w v u

namespace GlobalTheory.CompanionTheory.CosieveBC

open GlobalTheory.CompanionTheory.CosieveMV

section Cochains

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

abbrev cw (W : ObjectProperty C) : Cx.{max u v w} R := CH.cx (W.ι ⋙ F)

abbrev supP (U V : ObjectProperty C) : ObjectProperty C := fun T => U T ∨ V T

abbrev infP (U V : ObjectProperty C) : ObjectProperty C := fun T => U T ∧ V T

variable {U V : ObjectProperty C}

theorem le_supL : U ≤ supP U V := fun _ h => Or.inl h
theorem le_supR : V ≤ supP U V := fun _ h => Or.inr h
theorem inf_leL : infP U V ≤ U := fun _ h => h.1
theorem inf_leR : infP U V ≤ V := fun _ h => h.2

def liftW {W P : ObjectProperty C} (hP : Cosieve P) {n : ℕ} (t : ComposableArrows W.FullSubcategory n)
    (h : P (t.obj 0).obj) : ComposableArrows P.FullSubcategory n :=
  liftCh hP (t ⋙ W.ι) h

variable (U V)

def mvF : Cx.Hom (cw F (supP U V)) (prodCx (cw F U) (cw F V)) (RingHom.id R) where
  f n := LinearMap.prod ((resU F le_supL).pullC n) ((resU F le_supR).pullC n)
  comm n x := Prod.ext ((resU F le_supL).d_pullC n x) ((resU F le_supR).d_pullC n x)

def mvG : Cx.Hom (prodCx (cw F U) (cw F V)) (cw F (infP U V)) (RingHom.id R) where
  f n := ((resU F inf_leL).pullC n).comp (LinearMap.fst R _ _) - ((resU F inf_leR).pullC n).comp (LinearMap.snd R _ _)
  comm n x := by
    change CH.d _ n ((resU F inf_leL).pullC n x.1 - (resU F inf_leR).pullC n x.2) =
      (resU F inf_leL).pullC (n + 1) (CH.d _ n x.1) - (resU F inf_leR).pullC (n + 1) (CH.d _ n x.2)
    rw [map_sub, (resU F inf_leL).d_pullC, (resU F inf_leR).d_pullC]

variable {U V}

theorem mvF_inj (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Injective ((mvF F U V).f n) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  funext t
  rcases (t.obj 0).property with h | h
  · exact congrFun (congrArg Prod.fst hx) (liftW hU t h)
  · exact congrFun (congrArg Prod.snd hx) (liftW hV t h)

open Classical in
theorem mvFG_exact (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Exact ((mvF F U V).f n) ((mvG F U V).f n) := by
  intro y
  constructor
  · intro hy
    obtain ⟨a, b⟩ := y
    have hab : ∀ s : ComposableArrows (infP U V).FullSubcategory n,
        (resU F inf_leL).pullC n a s = (resU F inf_leR).pullC n b s := fun s =>
      sub_eq_zero.1 (congrFun hy s)
    refine ⟨fun t => if h : U (t.obj 0).obj then a (liftW hU t h) else
      b (liftW hV t ((t.obj 0).property.resolve_left h)), Prod.ext ?_ ?_⟩
    · funext s
      exact dif_pos (s.obj 0).property
    · funext s
      by_cases h : U (s.obj 0).obj
      · refine (dif_pos h).trans ?_
        exact hab (liftW (P := infP U V) (fun _ _ f h => ⟨hU f h.1, hV f h.2⟩) s ⟨h, (s.obj 0).property⟩)
      · exact dif_neg h
  · rintro ⟨x, rfl⟩
    refine sub_eq_zero.2 ?_
    rfl

open Classical in

def extV (hU : Cosieve U) (hV : Cosieve V) {n : ℕ} (y : CH.Cn ((infP U V).ι ⋙ F) n) : CH.Cn (U.ι ⋙ F) n :=
  fun t => if h : V (t.obj 0).obj then
    y (liftW (P := infP U V) (fun _ _ f h => ⟨hU f h.1, hV f h.2⟩) t ⟨(t.obj 0).property, h⟩) else 0

theorem mvG_surj (hU : Cosieve U) (hV : Cosieve V) (n : ℕ) : Function.Surjective ((mvG F U V).f n) := by
  intro y
  refine ⟨(extV F hU hV y, 0), funext fun s => ?_⟩
  have e1 : (resU F inf_leL).pullC n (extV F hU hV y) s = y s := dif_pos (s.obj 0).property.2
  have e2 : (resU F inf_leR).pullC n (0 : CH.Cn (V.ι ⋙ F) n) s = 0 := congrFun (map_zero _) s
  change (resU F inf_leL).pullC n (extV F hU hV y) s - (resU F inf_leR).pullC n (0 : CH.Cn (V.ι ⋙ F) n) s = y s
  rw [e1, e2, sub_zero]

end Cochains

section Family

universe w' v' u'

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] (G : C' ⥤ C) {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)] (F : ι → (C ⥤ ModuleCat.{w} R)) (F' : C' ⥤ ModuleCat.{w'} R')
  (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T)
  (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x, τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))

def Phi {W : ObjectProperty C} {W' : ObjectProperty C'} (h : ∀ T, W' T → W (G.obj T)) (i : ι) (n : N i) :
    Cx.Hom (cw (F i) W) (cw F' W') σ :=
  (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) h).hom

variable {G F F' τ hτ}

theorem phi_lin (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x) {W : ObjectProperty C} {W' : ObjectProperty C'}
    (h : ∀ T, W' T → W (G.obj T)) : Lin (Phi G F F' τ hτ h) :=
  ⟨fun i n n' k x => funext fun s => hadd i n n' _ _, fun i r n k x => funext fun s => hsm i r n _ _⟩

theorem lin_prod {K L : ι → Cx.{w} R} {K' L' : Cx.{w'} R'} {φ : ∀ i, N i → Cx.Hom (K i) K' σ}
    {ψ : ∀ i, N i → Cx.Hom (L i) L' σ} (hφ : Lin φ) (hψ : Lin ψ) : Lin fun i n => prodHom (φ i n) (ψ i n) :=
  ⟨fun i n n' k x => Prod.ext (hφ.1 i n n' k x.1) (hψ.1 i n n' k x.2),
    fun i r n k x => Prod.ext (hφ.2 i r n k x.1) (hψ.2 i r n k x.2)⟩

theorem bc_sup [Fintype ι] [DecidableEq ι] [∀ i, Module.Flat R (N i)]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x) {U V : ObjectProperty C} {U' V' : ObjectProperty C'}
    (hU : Cosieve U) (hV : Cosieve V) (hU' : Cosieve U') (hV' : Cosieve V')
    (hu : ∀ T, U' T → U (G.obj T)) (hv : ∀ T, V' T → V (G.obj T))
    (tU : BC (Phi G F F' τ hτ hu)) (tV : BC (Phi G F F' τ hτ hv))
    (tI : BC (Phi G F F' τ hτ (W := infP U V) (W' := infP U' V') fun T h => ⟨hu T h.1, hv T h.2⟩)) :
    BC (Phi G F F' τ hτ (W := supP U V) (W' := supP U' V') fun T h => h.imp (hu T) (hv T)) := by
  refine (bc_ses (fun i => mvF (F i) U V) (fun i => mvG (F i) U V) (mvF F' U' V') (mvG F' U' V')
    (fun i n => mvF_inj _ hU hV n) (fun i n => mvFG_exact _ hU hV n) (fun i n => mvG_surj _ hU hV n)
    (fun n => mvF_inj _ hU' hV' n) (fun n => mvFG_exact _ hU' hV' n) (fun n => mvG_surj _ hU' hV' n)
    _ (fun i n => prodHom (Phi G F F' τ hτ hu i n) (Phi G F F' τ hτ hv i n)) _
    (phi_lin hadd hsm _) (lin_prod (phi_lin hadd hsm _) (phi_lin hadd hsm _)) (phi_lin hadd hsm _)
    ?_ ?_).1 (bc_prod _ _ (phi_lin hadd hsm _) (phi_lin hadd hsm _) tU tV) tI
  · exact fun i m k x => rfl
  · intro i m k x
    funext s
    exact map_sub (τ i m _) _ _

end Family

end GlobalTheory.CompanionTheory.CosieveBC
