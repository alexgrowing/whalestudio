import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDOneZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.RepLifts
open GlobalTheory.CompanionTheory.CupRep

section Abs
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem d_cupList (A : C ⥤ CommAlgCat.{0} R) : ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF A) 1),
    (∀ k, CH.d _ 1 (ℓ k) = 0) → CH.d _ m (cupListC A ℓ) = 0
  | 0, _, _ => GlobalTheory.CompanionTheory.ConeCech.cech_d_one_zero A
  | m + 1, ℓ, h => by
    have e : cupListC A ℓ = (CH.mulP A).cupC (by omega) (cupListC A fun i => ℓ (Fin.castSucc i)) (ℓ (Fin.last m)) := rfl
    rw [e, CrystallineSemistableComparison.P.leibniz, d_cupList A _ fun i => h _, h]
    simp

variable {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

theorem cupList_mem (hF : IsFil Φ Fil) : ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1),
    (∀ k, ℓ k ∈ FC (Fil ((1 : ℕ) : ℤ)) 1) → cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m
  | 0, _, _ => mem_FC.2 fun s => by
      have e : (Fil ((0 : ℕ) : ℤ)).S (s.obj (Fin.last 0)) = ⊤ := hF.top _ (by simp) _
      rw [e]
      trivial
  | m + 1, ℓ, h => cup_mem hF (r := m) (r' := 1) rfl (cupList_mem hF _ fun i => h _) (h _)

theorem bd_cup (hF : IsFil Φ Fil) {m : ℕ} {g : CH.Cn (CH.modF Φ.A) m} (hg : IsBd Fil m g)
    {l : CH.Cn (CH.modF Φ.A) 1} (hl : l ∈ FC (Fil ((1 : ℕ) : ℤ)) 1) (hdl : CH.d _ 1 l = 0) :
    ∃ H : CH.Cn (CH.modF Φ.A) m, H ∈ FC (Fil ((m + 1 : ℕ) : ℤ)) m ∧
      (CH.mulP Φ.A).cupC (rfl : m + 1 = m + 1) g l = CH.d _ m H := by
  cases m with
  | zero =>
    have hg0 : g = 0 := hg
    subst hg0
    exact ⟨0, zero_mem _, by simp⟩
  | succ n =>
    obtain ⟨H, hH, rfl⟩ := hg
    refine ⟨(CH.mulP Φ.A).cupC (rfl : n + 1 = n + 1) H l, cup_mem hF rfl hH hl, ?_⟩
    rw [CrystallineSemistableComparison.P.leibniz, hdl]
    simp

theorem cup_d (hF : IsFil Φ Fil) {m : ℕ} {B : CH.Cn (CH.modF Φ.A) m} (hB : B ∈ FC (Fil (m : ℤ)) m)
    (hdB : CH.d _ m B = 0) {a : CH.Cn (CH.modF Φ.A) 0} (ha : a ∈ FC (Fil ((1 : ℕ) : ℤ)) 0) :
    ∃ H : CH.Cn (CH.modF Φ.A) m, H ∈ FC (Fil ((m + 1 : ℕ) : ℤ)) m ∧
      (CH.mulP Φ.A).cupC (rfl : m + 1 = m + 1) B (CH.d _ 0 a) = CH.d _ m H := by
  refine ⟨(-1 : ℤ) ^ m • (CH.mulP Φ.A).cupC (add_zero m) B a, zsmul_mem (cup_mem hF _ hB ha) _, ?_⟩
  rw [map_zsmul, CrystallineSemistableComparison.P.leibniz, hdB]
  simp only [map_zero, LinearMap.zero_apply, zero_add, smul_smul, ← mul_pow]
  simp

theorem cupList_diff (hF : IsFil Φ Fil) : ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1)
    (α : Fin m → CH.Cn (CH.modF Φ.A) 0), (∀ k, ℓ k ∈ FC (Fil ((1 : ℕ) : ℤ)) 1) → (∀ k, CH.d _ 1 (ℓ k) = 0) →
    (∀ k, α k ∈ FC (Fil ((1 : ℕ) : ℤ)) 0) →
    IsBd Fil m (cupListC Φ.A (fun k => ℓ k + CH.d _ 0 (α k)) - cupListC Φ.A ℓ)
  | 0, _, _, _, _, _ => sub_self _
  | m + 1, ℓ, α, hℓ, hd, hα => by
    have ih := cupList_diff hF (fun i : Fin m => ℓ i.castSucc) (fun i => α i.castSucc) (fun i => hℓ _)
      (fun i => hd _) (fun i => hα _)
    have hl' : ℓ (Fin.last m) + CH.d _ 0 (α (Fin.last m)) ∈ FC (Fil ((1 : ℕ) : ℤ)) 1 :=
      add_mem (hℓ _) (d_mem (hα _))
    have hdl' : CH.d _ 1 (ℓ (Fin.last m) + CH.d _ 0 (α (Fin.last m))) = 0 := by
      rw [map_add, hd, CH.d_d, add_zero]
    obtain ⟨H₁, hH₁, e₁⟩ := bd_cup hF ih hl' hdl'
    obtain ⟨H₂, hH₂, e₂⟩ := cup_d hF (cupList_mem hF (fun i : Fin m => ℓ i.castSucc) fun i => hℓ _)
      (d_cupList Φ.A _ fun i => hd _) (hα (Fin.last m))
    refine ⟨H₁ + H₂, add_mem hH₁ hH₂, ?_⟩
    rw [map_add, ← e₁, ← e₂]
    change (CH.mulP Φ.A).cupC rfl _ (ℓ (Fin.last m) + CH.d _ 0 (α (Fin.last m))) - (CH.mulP Φ.A).cupC rfl _ (ℓ (Fin.last m)) = _
    simp only [map_sub, map_add, LinearMap.sub_apply]
    abel

theorem rep_of_bd : ∀ {m : ℕ} {z z' : CH.Cn (CH.modF Φ.A) m} {c : CH.H (sq (Fil (m : ℤ)) (Fil ((m : ℤ) + 1))) m},
    IsBd Fil m (z' - z) → CrystallineSemistableComparison.Pb.Rep (Fil (m : ℤ)) (Fil ((m : ℤ) + 1)) z c →
    CrystallineSemistableComparison.Pb.Rep (Fil (m : ℤ)) (Fil ((m : ℤ) + 1)) z' c
  | 0, z, z', c, hb, h => by
    have e : z' = z := sub_eq_zero.1 hb
    rw [e]
    exact h
  | n + 1, z, z', c, hb, h => by
    obtain ⟨H, hH, e⟩ := hb
    have h2 := rep_add h (rep_d (a := Fil ((n + 1 : ℕ) : ℤ)) (b := Fil (((n + 1 : ℕ) : ℤ) + 1)) H (mem_FC.1 hH))
    rw [add_zero] at h2
    have e' : z' = z + CH.d _ n H := by rw [← e]; abel
    rw [e']
    exact h2

end Abs

section Conc
variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
  {Q : ObjectProperty (Thick (smFun X q))}

open GlobalTheory.CompanionTheory.ConeZcls

def rU (v : ∀ T : Q.FullSubcategory, T.obj.Bˣ) {T T' : Q.FullSubcategory} (f : T ⟶ T') : T'.obj.Bˣ :=
  v T' * (Units.map f.hom.φ.toMonoidHom (v T))⁻¹

def lg (s : ℕ) (v : ∀ T : Q.FullSubcategory, T.obj.Bˣ) {T T' : Q.FullSubcategory} (f : T ⟶ T') : T'.obj.B :=
  plogK T'.obj.δ s ((rU v f : T'.obj.B) - 1)

theorem grp1 {G : Type*} [CommGroup G] (a b c : G) : a * b⁻¹ = c * b⁻¹ * (a * c⁻¹) := by
  simp only [← div_eq_mul_inv]
  rw [div_mul_div_comm, mul_comm c a, mul_div_mul_right_eq_div]

theorem grp2 {G : Type*} [CommGroup G] (a b e e' : G) :
    a * e' * (b * e)⁻¹ = a * b⁻¹ * e' * e⁻¹ := by
  rw [mul_inv]
  simp only [mul_assoc]
  rw [mul_left_comm b⁻¹ e' e⁻¹]

theorem rU_comp (v : ∀ T : Q.FullSubcategory, T.obj.Bˣ) {T T' T'' : Q.FullSubcategory} (f : T ⟶ T') (g : T' ⟶ T'') :
    rU v (f ≫ g) = Units.map g.hom.φ.toMonoidHom (rU v f) * rU v g := by
  have h : Units.map (f ≫ g).hom.φ.toMonoidHom (v T) =
      Units.map g.hom.φ.toMonoidHom (Units.map f.hom.φ.toMonoidHom (v T)) := rfl
  unfold rU
  rw [h, map_mul, map_inv]
  exact grp1 _ _ _

theorem rU_sub_mem (v : ∀ T : Q.FullSubcategory, T.obj.Bˣ)
    (hv : ∀ (T T' : Q.FullSubcategory) (f : T ⟶ T'), (v T' : T'.obj.B) - f.hom.φ (v T) ∈ T'.obj.J)
    {T T' : Q.FullSubcategory} (f : T ⟶ T') : (rU v f : T'.obj.B) - 1 ∈ T'.obj.J := by
  have e : (rU v f : T'.obj.B) - 1 = ((v T' : T'.obj.B) - f.hom.φ (v T)) *
      (((Units.map f.hom.φ.toMonoidHom (v T))⁻¹ : T'.obj.Bˣ) : T'.obj.B) := by
    have h1 : f.hom.φ (v T) * (((Units.map f.hom.φ.toMonoidHom (v T))⁻¹ : T'.obj.Bˣ) : T'.obj.B) = 1 :=
      Units.mul_inv (Units.map f.hom.φ.toMonoidHom (v T))
    rw [sub_mul, h1]
    rfl
  rw [e]
  exact T'.obj.J.mul_mem_right _ (hv T T' f)

theorem map_sub_mem {T T' : Thick (smFun X q)} (f : T ⟶ T') (e : T.Bˣ) (he : (e : T.B) - 1 ∈ T.J) :
    ((Units.map f.φ.toMonoidHom e : T'.Bˣ) : T'.B) - 1 ∈ T'.J := by
  have h := f.hle he
  rw [Ideal.mem_comap, map_sub, map_one] at h
  exact h

theorem plog_map_unit {T T' : Thick (smFun X q)} (f : T ⟶ T') (s : ℕ) (e : T.Bˣ) (he : (e : T.B) - 1 ∈ T.J) :
    plogK T'.δ s (((Units.map f.φ.toMonoidHom e : T'.Bˣ) : T'.B) - 1) = f.φ (plogK T.δ s ((e : T.B) - 1)) := by
  rw [plogK_map f s he, map_sub, map_one]
  rfl

theorem lg_comp (s : ℕ) (hs : ∀ T : Q.FullSubcategory, T.obj.pdPow s = ⊥) (v : ∀ T : Q.FullSubcategory, T.obj.Bˣ)
    (hv : ∀ (T T' : Q.FullSubcategory) (f : T ⟶ T'), (v T' : T'.obj.B) - f.hom.φ (v T) ∈ T'.obj.J)
    {T T' T'' : Q.FullSubcategory} (f : T ⟶ T') (g : T' ⟶ T'') :
    lg s v (f ≫ g) = g.hom.φ (lg s v f) + lg s v g := by
  unfold lg
  rw [rU_comp, plog_mul _ s (hs _) _ _ (map_sub_mem g.hom _ (rU_sub_mem v hv f)) (rU_sub_mem v hv g),
    plog_map_unit g.hom s _ (rU_sub_mem v hv f)]

theorem lg_shift (s : ℕ) (hs : ∀ T : Q.FullSubcategory, T.obj.pdPow s = ⊥) (v e : ∀ T : Q.FullSubcategory, T.obj.Bˣ)
    (hv : ∀ (T T' : Q.FullSubcategory) (f : T ⟶ T'), (v T' : T'.obj.B) - f.hom.φ (v T) ∈ T'.obj.J)
    (he : ∀ T : Q.FullSubcategory, (e T : T.obj.B) - 1 ∈ T.obj.J)
    {T T' : Q.FullSubcategory} (f : T ⟶ T') :
    lg s (fun T => v T * e T) f = lg s v f +
      (plogK T'.obj.δ s ((e T' : T'.obj.B) - 1) - f.hom.φ (plogK T.obj.δ s ((e T : T.obj.B) - 1))) := by
  have h : rU (fun T => v T * e T) f = rU v f * e T' * (Units.map f.hom.φ.toMonoidHom (e T))⁻¹ := by
    unfold rU
    rw [map_mul]
    exact grp2 _ _ _ _
  have hr := rU_sub_mem v hv f
  have hm := map_sub_mem f.hom (e T) (he T)
  unfold lg
  rw [h, plog_mul _ s (hs _) _ _ (mul_sub_mem _ _ _ hr (he T')) (inv_sub _ _ hm),
    plog_mul _ s (hs _) _ _ hr (he T'), plog_inv _ s (hs _) _ hm, plog_map_unit f.hom s _ (he T)]
  ring

theorem dlogC_eq (s : ℕ) (v : ∀ T : Q.FullSubcategory, T.obj.Bˣ) (σ : ComposableArrows Q.FullSubcategory 1) :
    (show (σ.obj (Fin.last 1)).obj.B from dlogC Q s (fun T => (v T : T.obj.B)) σ) =
      lg s v (σ.map (homOfLE (Fin.zero_le (Fin.last 1)))) := by
  have e : Ring.inverse ((σ.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom.φ (v (σ.obj 0) : (σ.obj 0).obj.B)) =
      (((Units.map (σ.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom.φ.toMonoidHom (v (σ.obj 0)))⁻¹ :
        (σ.obj (Fin.last 1)).obj.Bˣ) : (σ.obj (Fin.last 1)).obj.B) :=
    Ring.inverse_unit (Units.map (σ.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom.φ.toMonoidHom (v (σ.obj 0)))
  change plogK _ s (_ * Ring.inverse _ - 1) = _
  rw [e]
  rfl

end Conc

section Main
variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
  {Q : ObjectProperty (Thick (smFun X q))}

open GlobalTheory.CompanionTheory.ConeZcls

theorem plogK_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) {x : B} (hx : x ∈ J) :
    plogK δ s x ∈ J :=
  J.sum_mem fun k _ => J.mul_mem_left _ (δ.dpow_mem (Nat.succ_ne_zero k) hx)

theorem d_dlogC (s : ℕ) (hs : ∀ T : Q.FullSubcategory, T.obj.pdPow s = ⊥) (v : ∀ T : Q.FullSubcategory, T.obj.Bˣ)
    (hv : ∀ (T T' : Q.FullSubcategory) (f : T ⟶ T'), (v T' : T'.obj.B) - f.hom.φ (v T) ∈ T'.obj.J) :
    CH.d _ 1 (dlogC Q s fun T => (v T : T.obj.B)) = 0 := by
  funext σ
  have key := lg_comp s hs v hv (σ.map' 0 1) (σ.map' 1 2)
  rw [← composable_arrows_map_zero_two σ] at key
  have h0 : ((CH.modF (sP Q).A).map (toLast 0 σ)).hom (dlogC Q s (fun T => (v T : T.obj.B)) (face 0 σ)) =
      (show (σ.obj (Fin.last 2)).obj.B from lg s v (σ.map' 1 2)) :=
    (map_self (CH.modF (sP Q).A) σ (Fin.last 2) _ _).trans (dlogC_eq s v (face 0 σ))
  have h1 : ((CH.modF (sP Q).A).map (toLast 1 σ)).hom (dlogC Q s (fun T => (v T : T.obj.B)) (face 1 σ)) =
      (show (σ.obj (Fin.last 2)).obj.B from lg s v (σ.map' 0 2)) :=
    (map_self (CH.modF (sP Q).A) σ (Fin.last 2) _ _).trans (dlogC_eq s v (face 1 σ))
  have h2 : ((CH.modF (sP Q).A).map (toLast 2 σ)).hom (dlogC Q s (fun T => (v T : T.obj.B)) (face 2 σ)) =
      (show (σ.obj (Fin.last 2)).obj.B from (σ.map' 1 2).hom.φ (lg s v (σ.map' 0 1))) :=
    congrArg (σ.map' 1 2).hom.φ (dlogC_eq s v (face 2 σ))
  have hd : CH.d (CH.modF (sP Q).A) 1 (dlogC Q s fun T => (v T : T.obj.B)) σ =
      ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ((CH.modF (sP Q).A).map (toLast i σ)).hom
        (dlogC Q s (fun T => (v T : T.obj.B)) (face i σ)) := rfl
  rw [hd, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, even_two, Even.neg_pow, one_pow]
  rw [h0, h1, h2]
  change lg s v (σ.map' 1 2) + -lg s v (σ.map' 0 2) + (σ.map' 1 2).hom.φ (lg s v (σ.map' 0 1)) = 0
  rw [key]
  ring

theorem map_self1 {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} K) (σ : ComposableArrows C 1) (i : Fin 2)
    (h : i ⟶ i) (x : F.obj (σ.obj i)) : (F.map (σ.map h)).hom x = x := by
  rw [Subsingleton.elim h (𝟙 _), σ.map_id, F.map_id]
  rfl

theorem d_zeroC (a : ∀ T : Q.FullSubcategory, T.obj.B) (σ : ComposableArrows Q.FullSubcategory 1) :
    (show (σ.obj (Fin.last 1)).obj.B from CH.d _ 0 (zeroC Q a) σ) =
      a (σ.obj (Fin.last 1)) - (σ.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom.φ (a (σ.obj 0)) := by
  have hd : CH.d (CH.modF (sP Q).A) 0 (zeroC Q a) σ =
      ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ((CH.modF (sP Q).A).map (toLast i σ)).hom (zeroC Q a (face i σ)) := rfl
  have h0 : ((CH.modF (sP Q).A).map (toLast 0 σ)).hom (zeroC Q a (face 0 σ)) =
      (show (σ.obj (Fin.last 1)).obj.B from a (σ.obj (Fin.last 1))) := by
    exact map_self1 (CH.modF (sP Q).A) σ (Fin.last 1) _ _
  have h1 : ((CH.modF (sP Q).A).map (toLast 1 σ)).hom (zeroC Q a (face 1 σ)) =
      (show (σ.obj (Fin.last 1)).obj.B from (σ.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom.φ (a (σ.obj 0))) := rfl
  change (show (σ.obj (Fin.last 1)).obj.B from CH.d (CH.modF (sP Q).A) 0 (zeroC Q a) σ) = _
  rw [hd, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  rw [h0, h1]
  exact sub_eq_add_neg _ _ |>.symm

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
    (Q : ObjectProperty (Thick (smFun X q))) (s : ℕ), (∀ T, Q T → T.pdPow s = ⊥) → ∀ {m : ℕ}
    (ĝ ĝ' : Fin m → ∀ T : Q.FullSubcategory, T.obj.B),
    (∀ k T, IsUnit (ĝ k T)) →
    (∀ k (T T' : Q.FullSubcategory) (f : T ⟶ T'), ĝ k T' - f.hom.φ (ĝ k T) ∈ T'.obj.J) →
    (∀ k T, ĝ k T - ĝ' k T ∈ T.obj.J) →
    ∀ c, Rep (sFil Q m) (sFil Q ((m : ℤ) + 1)) (cupListC (sP Q).A fun k => dlogC Q s (ĝ k)) c →
      Rep (sFil Q m) (sFil Q ((m : ℤ) + 1)) (cupListC (sP Q).A fun k => dlogC Q s (ĝ' k)) c := by
  intro K _ _ X q Q s hs m ĝ ĝ' hu hc hJ c hrep
  have hs' : ∀ T : Q.FullSubcategory, T.obj.pdPow s = ⊥ := fun T => hs _ T.property
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil Q
  choose v hv using hu
  obtain rfl : ĝ = fun k T => (v k T : T.obj.B) := by
    funext k T
    exact (hv k T).symm
  have hun : ∀ (T : Q.FullSubcategory) (x : T.obj.B), x ∈ T.obj.J → IsUnit (1 + x) := by
    intro T x hx
    have hn : IsNilpotent x := by
      obtain ⟨n, hn⟩ := J_nil T.obj
      refine ⟨n, ?_⟩
      have h1 : x ^ n ∈ T.obj.J ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at h1
      simpa using h1
    exact hn.isUnit_one_add
  have he : ∀ k (T : Q.FullSubcategory), ∃ e : T.obj.Bˣ, (e : T.obj.B) - 1 ∈ T.obj.J ∧
      ĝ' k T = ((v k T * e : T.obj.Bˣ) : T.obj.B) := by
    intro k T
    have hx : -(((v k T)⁻¹ : T.obj.Bˣ) : T.obj.B) * ((v k T : T.obj.B) - ĝ' k T) ∈ T.obj.J :=
      T.obj.J.mul_mem_left _ (hJ k T)
    obtain ⟨e, he⟩ := hun T _ hx
    refine ⟨e, by rw [he, add_sub_cancel_left]; exact hx, ?_⟩
    have hvi : (v k T : T.obj.B) * (((v k T)⁻¹ : T.obj.Bˣ) : T.obj.B) = 1 := Units.mul_inv _
    rw [Units.val_mul, he]
    linear_combination ((v k T : T.obj.B) - ĝ' k T) * hvi
  choose e he1 he2 using he
  obtain rfl : ĝ' = fun k T => ((v k T * e k T : T.obj.Bˣ) : T.obj.B) := by
    funext k T
    exact he2 k T
  let a : Fin m → ∀ T : Q.FullSubcategory, T.obj.B := fun k T => plogK T.obj.δ s ((e k T : T.obj.B) - 1)
  let α : Fin m → CH.Cn (CH.modF (sP Q).A) 0 := fun k => zeroC Q (a k)
  have key : (fun k => dlogC Q s fun T => ((v k T * e k T : T.obj.Bˣ) : T.obj.B)) =
      fun k => dlogC Q s (fun T => (v k T : T.obj.B)) + CH.d _ 0 (α k) := by
    funext k
    funext σ
    have a1 := dlogC_eq s (fun T => v k T * e k T) σ
    have a2 := dlogC_eq s (v k) σ
    have a3 := lg_shift s hs' (v k) (e k) (hc k) (he1 k) (σ.map (homOfLE (Fin.zero_le (Fin.last 1))))
    have a4 := d_zeroC (a k) σ
    refine a1.trans (a3.trans ?_)
    rw [← a2]
    exact congrArg _ a4.symm
  have hm1 : ∀ k, dlogC Q s (fun T => (v k T : T.obj.B)) ∈ FC (sFil Q ((1 : ℕ) : ℤ)) 1 := by
    intro k
    refine mem_FC.2 fun σ => ?_
    rw [Nat.cast_one, hF.one]
    have e1 := dlogC_eq s (v k) σ
    change (show (σ.obj (Fin.last 1)).obj.B from dlogC Q s (fun T => (v k T : T.obj.B)) σ) ∈ (σ.obj (Fin.last 1)).obj.J
    rw [e1]
    exact plogK_mem _ _ (rU_sub_mem (v k) (hc k) _)
  have hd : ∀ k, CH.d _ 1 (dlogC Q s fun T => (v k T : T.obj.B)) = 0 := fun k => d_dlogC s hs' (v k) (hc k)
  have hα : ∀ k, α k ∈ FC (sFil Q ((1 : ℕ) : ℤ)) 0 := by
    intro k
    refine mem_FC.2 fun σ => ?_
    rw [Nat.cast_one, hF.one]
    exact plogK_mem _ _ (he1 k _)
  rw [key]
  exact rep_of_bd (cupList_diff hF _ α hm1 hd hα) hrep

end Main

section Lifts
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
  {Q : ObjectProperty (Thick (smFun X q))}

theorem lift_compat {V : X.Opens} (hQ : ∀ T, Q T → InU V T) (g : Γ(X, V)) (ĝ : ∀ T : Q.FullSubcategory, T.obj.B)
    (hĝ : ∀ T : Q.FullSubcategory, Ideal.Quotient.mk T.obj.J (ĝ T) = ev T.obj (hQ _ T.property) g)
    (T T' : Q.FullSubcategory) (f : T ⟶ T') : ĝ T' - f.hom.φ (ĝ T) ∈ T'.obj.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [hĝ T', GlobalTheory.CompanionTheory.GrForm.ev_nat f.hom (hQ _ T.property) (hQ _ T'.property) g, ← hĝ T]
  rfl

end Lifts

end GlobalTheory.CompanionTheory.RepLifts
