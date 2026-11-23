import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubeRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalFrameThetaRelation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz.CubeNorm
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayHoriz.CubeNorm.SymMul

section Jets

variable {S : Type} [CommRing S] {ρ : Type}

theorem jetMap_mk' {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' S) (hφ : ∀ i, φ i ∈ orig S κ')
    (p : MvPolynomial κ S) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ p) := rfl

theorem jet_ext {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra S A] {f g : Jet S κ m →ₐ[S] A}
    (h : ∀ r, f (Ideal.Quotient.mk _ (MvPolynomial.X r)) = g (Ideal.Quotient.mk _ (MvPolynomial.X r))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

def wv (a b : S) : Fin 2 → ρ → S := ![fun _ => a, fun _ => b]

def linK {K K' : Type} [Fintype K'] (A : K → K' → S) (m : ℕ) : Jet S (K × ρ) m →ₐ[S] Jet S (K' × ρ) m :=
  jetMap (fun p => ∑ j, MvPolynomial.C (A p.1 j) * MvPolynomial.X (j, p.2)) fun p =>
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (X_mem_orig (j, p.2))

def subA : Fin 3 → Fin 2 → S := ![![1, 0], ![-1, 0], ![0, -1]]

def subB : Fin 3 → Fin 2 → S := ![![0, 1], ![0, -1], ![1, 0]]

def dneg (m : ℕ) : Jet S (Fin 2 × ρ) m →ₐ[S] Jet S ρ m :=
  jetMap (fun p => MvPolynomial.C (![1, -1] p.1 : S) * MvPolynomial.X p.2) fun p =>
    Ideal.mul_mem_left _ _ (X_mem_orig p.2)

macro "jet_tac" : tactic => `(tactic| (
  refine jet_ext fun r => ?_
  simp only [AlgHom.comp_apply, jetSum, jetIn, jetScale, linK, dneg, GlobalTheory.RayHoriz.jetW, jetMap_mk', AlgHom.id_apply]
  refine congrArg _ ?_
  simp [Finset.sum_insert, Fin.sum_univ_two, Fin.sum_univ_three, wv, subA, subB]
  try ring))

variable (m : ℕ)

theorem in0 : (jetIn (0 : Fin 2) : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m) = GlobalTheory.RayHoriz.jetW (wv 1 0) m := by jet_tac
theorem in1 : (jetIn (1 : Fin 2) : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m) = GlobalTheory.RayHoriz.jetW (wv 0 1) m := by jet_tac
theorem sumU : (jetSum (Finset.univ : Finset (Fin 2)) : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m) = GlobalTheory.RayHoriz.jetW (wv 1 1) m := by jet_tac
theorem in0n : (jetIn (0 : Fin 2) : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m).comp (jetScale fun _ => (-1 : S)) =
    GlobalTheory.RayHoriz.jetW (wv (-1) 0) m := by jet_tac
theorem in1n : (jetIn (1 : Fin 2) : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m).comp (jetScale fun _ => (-1 : S)) =
    GlobalTheory.RayHoriz.jetW (wv 0 (-1)) m := by jet_tac
theorem sumUn : (jetSum (Finset.univ : Finset (Fin 2)) : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m).comp (jetScale fun _ => (-1 : S)) =
    GlobalTheory.RayHoriz.jetW (wv (-1) (-1)) m := by jet_tac
theorem in_sum (k : Fin 2) : (jetIn k : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m) = jetSum {k} := by jet_tac

theorem ptA_0 : (linK (ρ := ρ) (subA (S := S)) m).comp (jetIn 0) = GlobalTheory.RayHoriz.jetW (wv 1 0) m := by jet_tac
theorem ptA_1 : (linK (ρ := ρ) (subA (S := S)) m).comp (jetIn 1) = GlobalTheory.RayHoriz.jetW (wv (-1) 0) m := by jet_tac
theorem ptA_2 : (linK (ρ := ρ) (subA (S := S)) m).comp (jetIn 2) = GlobalTheory.RayHoriz.jetW (wv 0 (-1)) m := by jet_tac
theorem ptB_0 : (linK (ρ := ρ) (subB (S := S)) m).comp (jetIn 0) = GlobalTheory.RayHoriz.jetW (wv 0 1) m := by jet_tac
theorem ptB_1 : (linK (ρ := ρ) (subB (S := S)) m).comp (jetIn 1) = GlobalTheory.RayHoriz.jetW (wv 0 (-1)) m := by jet_tac
theorem ptB_2 : (linK (ρ := ρ) (subB (S := S)) m).comp (jetIn 2) = GlobalTheory.RayHoriz.jetW (wv 1 0) m := by jet_tac

theorem cubA_e : (linK (ρ := ρ) (subA (S := S)) m).comp (jetSum ∅) = GlobalTheory.RayHoriz.jetW (wv 0 0) m := by jet_tac
theorem cubA_0 : (linK (ρ := ρ) (subA (S := S)) m).comp (jetSum {0}) = GlobalTheory.RayHoriz.jetW (wv 1 0) m := by jet_tac
theorem cubA_1 : (linK (ρ := ρ) (subA (S := S)) m).comp (jetSum {1}) = GlobalTheory.RayHoriz.jetW (wv (-1) 0) m := by jet_tac
theorem cubA_2 : (linK (ρ := ρ) (subA (S := S)) m).comp (jetSum {2}) = GlobalTheory.RayHoriz.jetW (wv 0 (-1)) m := by jet_tac
theorem cubA_01 : (linK (ρ := ρ) (subA (S := S)) m).comp (jetSum {0, 1}) = GlobalTheory.RayHoriz.jetW (wv 0 0) m := by jet_tac
theorem cubA_02 : (linK (ρ := ρ) (subA (S := S)) m).comp (jetSum {0, 2}) = GlobalTheory.RayHoriz.jetW (wv 1 (-1)) m := by jet_tac
theorem cubA_12 : (linK (ρ := ρ) (subA (S := S)) m).comp (jetSum {1, 2}) = GlobalTheory.RayHoriz.jetW (wv (-1) (-1)) m := by jet_tac
theorem linear_sub_a_comp_jetSum_all : (linK (ρ := ρ) (subA (S := S)) m).comp (jetSum {0, 1, 2}) = GlobalTheory.RayHoriz.jetW (wv 0 (-1)) m := by jet_tac
theorem cubB_e : (linK (ρ := ρ) (subB (S := S)) m).comp (jetSum ∅) = GlobalTheory.RayHoriz.jetW (wv 0 0) m := by jet_tac
theorem cubB_0 : (linK (ρ := ρ) (subB (S := S)) m).comp (jetSum {0}) = GlobalTheory.RayHoriz.jetW (wv 0 1) m := by jet_tac
theorem cubB_1 : (linK (ρ := ρ) (subB (S := S)) m).comp (jetSum {1}) = GlobalTheory.RayHoriz.jetW (wv 0 (-1)) m := by jet_tac
theorem cubB_2 : (linK (ρ := ρ) (subB (S := S)) m).comp (jetSum {2}) = GlobalTheory.RayHoriz.jetW (wv 1 0) m := by jet_tac
theorem cubB_01 : (linK (ρ := ρ) (subB (S := S)) m).comp (jetSum {0, 1}) = GlobalTheory.RayHoriz.jetW (wv 0 0) m := by jet_tac
theorem cubB_02 : (linK (ρ := ρ) (subB (S := S)) m).comp (jetSum {0, 2}) = GlobalTheory.RayHoriz.jetW (wv 1 1) m := by jet_tac
theorem cubB_12 : (linK (ρ := ρ) (subB (S := S)) m).comp (jetSum {1, 2}) = GlobalTheory.RayHoriz.jetW (wv 1 (-1)) m := by jet_tac
theorem linear_sub_b_comp_jetSum_all : (linK (ρ := ρ) (subB (S := S)) m).comp (jetSum {0, 1, 2}) = GlobalTheory.RayHoriz.jetW (wv 1 0) m := by jet_tac

theorem dneg_sum : (dneg (S := S) (ρ := ρ) m).comp (jetSum Finset.univ) = (Algebra.ofId S (Jet S ρ m)).comp jetAug := by
  refine jet_ext fun r => ?_
  simp only [AlgHom.comp_apply, jetSum, dneg, jetMap_mk']
  simp [jetAug, liftJet, Fin.sum_univ_two]

theorem jet_negation_comp_jetIn_zero : (dneg (S := S) (ρ := ρ) m).comp (jetIn 0) = AlgHom.id S (Jet S ρ m) := by jet_tac
theorem jet_negation_comp_jetIn_one : (dneg (S := S) (ρ := ρ) m).comp (jetIn 1) = jetScale fun _ => (-1 : S) := by jet_tac

end Jets

section Pts

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ]

theorem homAt_comp' {A B A' : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing A']
    [Algebra S A'] (f : A →ₐ[S] B) (g : A' →ₐ[S] A) : homAt x0 f ≫ homAt x0 g = homAt x0 (f.comp g) := by
  apply Over.OverMorphism.ext
  simp only [Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem homAt_id' {A : Type} [CommRing A] [Algebra S A] : homAt x0 (AlgHom.id S A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp [Formalism.L2.Pj.homAt, spMap]

theorem comp_one_ {T T' : Over X} (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem neg_pt {O : Type} [CommRing O] (a : OAct O G) (ch : ρ → O →+* S) (u : ρ → (Sp (DualNumber S) ⟶ G.left))
    (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (hx : IsExp a x0 ch u x) (m : ℕ) :
    homAt x0 (jetScale fun _ => (-1 : S) : Jet S ρ m →ₐ[S] Jet S ρ m) ≫ x m = (x m)⁻¹ := by
  have L := congrArg (homAt x0 (dneg (S := S) (ρ := ρ) m) ≫ ·) (hx.law m)
  rw [← Category.assoc, homAt_comp', dneg_sum, ← homAt_comp', Category.assoc, hx.zero, comp_one_, MonObj.comp_mul,
    ← Category.assoc, ← Category.assoc, homAt_comp', homAt_comp', jet_negation_comp_jetIn_zero, jet_negation_comp_jetIn_one, homAt_id', Category.id_comp] at L
  exact eq_inv_of_mul_eq_one_right L.symm

end Pts

section Vals

theorem val_stalk' {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : W ⟶ Z) (r : Z ⟶ Y) {w : W} {J : (W ⟶ X) → L.ι} (hJ : Good L w J) :
    Units.map (κ.stalkMap w).hom.toMonoidHom (val t r (κ w) fun ψ => J (κ ≫ ψ)) = val t (κ ≫ r) w J := by
  rw [val_of t (κ ≫ r) w J (fun k => J (κ ≫ r ≫ φ k)) fun k => by rw [Category.assoc]]
  have h : r (κ w) ∈ LB.wchart L φ fun k => J (κ ≫ r ≫ φ k) := Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)
  exact Units.ext ((congrArg (κ.stalkMap w).hom (gm_val r (κ w) _ h _)).trans
    ((Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ (LB.wchart L φ fun k => J (κ ≫ r ≫ φ k))) w h _).trans
      (gm_val (κ ≫ r) w _ h _).symm))

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] {L : LB G.left}

theorem symPull (σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]))
    (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) (H : MvPowerSeries ρ S) (hS : SymRatio x0 L σ x e H)
    {K : Type} (m : ℕ) (φ : Jet S ρ m →ₐ[S] Jet S K m) (y : (overAt x0 (Jet S K m)).left)
    (J : ((overAt x0 (Jet S K m)).left ⟶ G.left) → L.ι) (hJ : Good L y J) :
    (val σ (homAt x0 φ ≫ x m).left y J).val = gs (𝟙 _) y ⊤ (toΓ _ (φ (psJet m H))) *
      (val (e m) (homAt x0 (φ.comp (jetScale fun _ => (-1 : S)))).left y J *
        (val (e m) (homAt x0 φ).left y J)⁻¹).val := by
  have hJ' : Good L ((homAt x0 φ).left y) (fun ψ => J ((homAt x0 φ).left ≫ ψ)) := fun ψ => hJ _
  have h1 := hS m _ _ hJ'
  have e1 := val_stalk' σ (homAt x0 φ).left (x m).left hJ
  have e2 := val_stalk' (e m) (homAt x0 φ).left (homAt x0 (jetScale fun _ => (-1 : S))).left hJ
  have e3 := val_stalk' (e m) (homAt x0 φ).left (𝟙 _) hJ
  rw [← Over.comp_left, homAt_comp'] at e2
  rw [Category.comp_id] at e3
  have e4 : ((homAt x0 φ).left.stalkMap y).hom (gs (𝟙 _) ((homAt x0 φ).left y) ⊤ (toΓ _ (psJet m H))) =
      gs (𝟙 _) y ⊤ (toΓ _ (φ (psJet m H))) := by
    rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_comp (homAt x0 φ).left (𝟙 _) y ⊤ trivial, Category.comp_id]
    exact CocRatio.gs_spMap _ y _
  rw [Over.comp_left, ← e1, ← e2, ← e3, ← map_inv, ← map_mul, Units.coe_map, Units.coe_map, h1]
  simp only [MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_mul, e4]

theorem thetaPull (t : LB.Gen (Theta G L)) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x)
    (hT : GlobalTheory.RayHoriz.ThetaIs x0 L t x e) {K : Type} (m : ℕ) (ψ : Jet S (Fin 3 × ρ) m →ₐ[S] Jet S K m)
    (y : (overAt x0 (Jet S K m)).left) (J : ((overAt x0 (Jet S K m)).left ⟶ G.left) → L.ι) (hJ : Good L y J) :
    val t (homAt x0 ψ ≫ GlobalTheory.RayHoriz.pt3 x0 x m).left y J =
      ∏ I : Finset (Fin 3), val (e m) (homAt x0 (ψ.comp (jetSum I))).left y J ^ ((-1 : ℤ) ^ (3 - I.card)) := by
  have hJ' : Good L ((homAt x0 ψ).left y) (fun ψ' => J ((homAt x0 ψ).left ≫ ψ')) := fun ψ' => hJ _
  rw [Over.comp_left, ← val_stalk' t (homAt x0 ψ).left _ hJ, hT m _ _ hJ', map_prod]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [map_zpow, val_stalk' (e m) (homAt x0 ψ).left _ hJ, ← Over.comp_left, homAt_comp']

end Vals

theorem prod3 {M : Type} [CommGroup M] (f : Finset (Fin 3) → M) :
    ∏ I : Finset (Fin 3), f I ^ ((-1 : ℤ) ^ (3 - I.card)) =
      f ∅ ^ (-1 : ℤ) * (f {0} * (f {1} * (f {2} * (f {0, 1} ^ (-1 : ℤ) * (f {0, 2} ^ (-1 : ℤ) *
        (f {1, 2} ^ (-1 : ℤ) * f {0, 1, 2})))))) := by
  have hu : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by
    decide
  rw [hu]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp [Finset.card_insert_of_notMem]

theorem sumSer_psJet {S : Type} [CommRing S] {ρ : Type} [Fintype ρ] [DecidableEq ρ] {K : Type} [Fintype K]
    [DecidableEq K] (m : ℕ) (I : Finset K) (h : MvPowerSeries ρ S) :
    (jetSum I : Jet S ρ m →ₐ[S] Jet S (K × ρ) m) (psJet m h) = psJet m (sumSer I h) := by
  have ha : ∀ r, MvPowerSeries.constantCoeff (∑ i ∈ I, (MvPowerSeries.X (i, r) : MvPowerSeries (K × ρ) S)) = 0 := by
    intro r; rw [map_sum]; exact Finset.sum_eq_zero fun i _ => MvPowerSeries.constantCoeff_X _
  rw [sumSer, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_subst m _ ha]
  refine congrArg (fun f : Jet S ρ m →ₐ[S] Jet S (K × ρ) m => f (psJet m h)) (jet_ext fun r => ?_)
  simp only [jetSum, jetMap_mk', MvPolynomial.aeval_X]
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq]
  have : (∑ i ∈ I, (MvPowerSeries.X (i, r) : MvPowerSeries (K × ρ) S)) =
      ((∑ i ∈ I, MvPolynomial.X (i, r) : MvPolynomial (K × ρ) S) : MvPowerSeries (K × ρ) S) := by
    clear ha
    induction I using Finset.induction_on with
    | empty => simp
    | insert a s hna ih => rw [Finset.sum_insert hna, Finset.sum_insert hna, ih, MvPolynomial.coe_add, MvPolynomial.coe_X]
  rw [this, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe]

theorem alg_helper {A : Type} [CommRing A] {g g0 g1 : A} {p c1 q r c2 : Aˣ}
    (h : g * p.val * c1.val = g0 * q.val * (g1 * r.val) * c2.val) (hw : p * c1 = q * r * c2) : g = g0 * g1 := by
  have h' : g * (p * c1).val = g0 * g1 * (q * r * c2).val := by
    simp only [Units.val_mul]; linear_combination h
  rw [hw] at h'
  exact (Units.mul_left_inj _).1 h'

theorem in_psJet {S : Type} [CommRing S] {ρ : Type} [Fintype ρ] [DecidableEq ρ] (m : ℕ) (k : Fin 2)
    (h : MvPowerSeries ρ S) :
    (jetIn k : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m) (psJet m h) = psJet m (sumSer {k} h) := by
  rw [in_sum, sumSer_psJet]

theorem symRatio_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (E : Type) [Field E] [NumberField E]
    [StarRing (𝓞 E)] [Module (𝓞 E) D.X] (oa : D.OAct (𝓞 E)) (S : Type) [Field S] [CharZero S] (x0 : Sp S ⟶ Sp R)
    (ρ : Type) [Fintype ρ] [DecidableEq ρ] (ch : ρ → 𝓞 E →+* S) (u : ρ → (Sp (DualNumber S) ⟶ D.P.A.left))
    (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ D.P.A), IsExp (Ray.actB oa) x0 ch u x → ∀ (e : Fr x0 D.P.L x)
    (H : MvPowerSeries ρ S), GlobalTheory.RayHoriz.IsRigFr x0 D.P.L D.rig x e → GlobalTheory.RayHoriz.ThetaIs x0 D.P.L D.cub.t x e →
    SymRatio x0 D.P.L D.sym x e H → sumSer (Finset.univ : Finset (Fin 2)) H = sumSer {0} H * sumSer {1} H := by
  intro R _ _ D E _ _ _ _ oa S _ _ x0 ρ _ _ ch u x hx e H _ hT hS
  refine Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.psJet_inj fun m => Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.toΓ_injective _ (fn_ext fun y _ => ?_)
  obtain ⟨J, hJ⟩ : ∃ J : ((overAt x0 (Jet S (Fin 2 × ρ) m)).left ⟶ D.P.A.left) → D.P.L.ι, Good D.P.L y J :=
    ⟨fun ψ => (Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.exists_chart D.P.L D.P.isLB (ψ y)).choose,
      fun ψ => (Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.exists_chart D.P.L D.P.isLB (ψ y)).choose_spec⟩
  have hneg := neg_pt x0 (Ray.actB oa) ch u x hx m
  have hXY : (homAt x0 (jetIn (0 : Fin 2)) ≫ x m) * (homAt x0 (jetIn (1 : Fin 2)) ≫ x m) =
      homAt x0 (jetSum (Finset.univ : Finset (Fin 2))) ≫ x m := (hx.law m).symm
  have hXi : (homAt x0 (jetIn (0 : Fin 2)) ≫ x m)⁻¹ =
      homAt x0 (GlobalTheory.RayHoriz.jetW (wv (-1) 0) m : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m) ≫ x m := by
    rw [← in0n, ← homAt_comp', Category.assoc, hneg]; exact (map_inv (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom _) (x m)).symm
  have hYi : (homAt x0 (jetIn (1 : Fin 2)) ≫ x m)⁻¹ =
      homAt x0 (GlobalTheory.RayHoriz.jetW (wv 0 (-1)) m : Jet S ρ m →ₐ[S] Jet S (Fin 2 × ρ) m) ≫ x m := by
    rw [← in1n, ← homAt_comp', Category.assoc, hneg]; exact (map_inv (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom _) (x m)).symm
  have hc1 : lift (homAt x0 (jetIn (0 : Fin 2)) ≫ x m) (lift (homAt x0 (jetIn (0 : Fin 2)) ≫ x m)⁻¹
      (homAt x0 (jetIn (1 : Fin 2)) ≫ x m)⁻¹) = homAt x0 (linK subA m) ≫ GlobalTheory.RayHoriz.pt3 x0 x m := by
    rw [hXi, hYi, in0, GlobalTheory.RayHoriz.pt3, comp_lift, comp_lift, ← Category.assoc, ← Category.assoc, ← Category.assoc,
      homAt_comp', homAt_comp', homAt_comp', ptA_0, ptA_1, ptA_2]
  have hc2 : lift (homAt x0 (jetIn (1 : Fin 2)) ≫ x m) (lift (homAt x0 (jetIn (1 : Fin 2)) ≫ x m)⁻¹
      (homAt x0 (jetIn (0 : Fin 2)) ≫ x m)) = homAt x0 (linK subB m) ≫ GlobalTheory.RayHoriz.pt3 x0 x m := by
    rw [hYi, in1, in0, GlobalTheory.RayHoriz.pt3, comp_lift, comp_lift, ← Category.assoc, ← Category.assoc, ← Category.assoc,
      homAt_comp', homAt_comp', homAt_comp', ptB_0, ptB_1, ptB_2]
  have key := GlobalTheory.GaugeValues.val_sym_mul D GlobalTheory.ExpansionTotal.globalFns hJ (homAt x0 (jetIn (0 : Fin 2)) ≫ x m)
    (homAt x0 (jetIn (1 : Fin 2)) ≫ x m)
  rw [hXY] at key
  have k' := congrArg Units.val key
  simp only [Units.val_mul] at k'
  rw [symPull x0 D.sym x e H hS m _ y J hJ, symPull x0 D.sym x e H hS m _ y J hJ,
    symPull x0 D.sym x e H hS m _ y J hJ, sumSer_psJet, in_psJet, in_psJet] at k'
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.psJet_mul, map_mul, gs_mul (𝟙 _) y ⊤ trivial]
  refine alg_helper k' ?_
  have cubeA : cubV D.cub y J (homAt x0 (jetIn (0 : Fin 2)) ≫ x m) (homAt x0 (jetIn (0 : Fin 2)) ≫ x m)⁻¹
      (homAt x0 (jetIn (1 : Fin 2)) ≫ x m)⁻¹ = ∏ I : Finset (Fin 3),
        val (e m) (homAt x0 ((linK subA m).comp (jetSum I))).left y J ^ ((-1 : ℤ) ^ (3 - I.card)) := by
    unfold cubV; rw [hc1]; exact thetaPull x0 D.cub.t x e hT m _ y J hJ
  have cubeB : cubV D.cub y J (homAt x0 (jetIn (1 : Fin 2)) ≫ x m) (homAt x0 (jetIn (1 : Fin 2)) ≫ x m)⁻¹
      (homAt x0 (jetIn (0 : Fin 2)) ≫ x m) = ∏ I : Finset (Fin 3),
        val (e m) (homAt x0 ((linK subB m).comp (jetSum I))).left y J ^ ((-1 : ℤ) ^ (3 - I.card)) := by
    unfold cubV; rw [hc2]; exact thetaPull x0 D.cub.t x e hT m _ y J hJ
  rw [cubeA, cubeB, prod3, prod3]
  beta_reduce
  simp only [cubA_e, cubA_0, cubA_1, cubA_2, cubA_01, cubA_02, cubA_12, linear_sub_a_comp_jetSum_all, cubB_e, cubB_0, cubB_1, cubB_2, cubB_01, cubB_02, cubB_12, linear_sub_b_comp_jetSum_all]
  rw [sumUn, sumU, in0n, in1n, in0, in1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

end GlobalTheory.RayHoriz.CubeNorm.SymMul
