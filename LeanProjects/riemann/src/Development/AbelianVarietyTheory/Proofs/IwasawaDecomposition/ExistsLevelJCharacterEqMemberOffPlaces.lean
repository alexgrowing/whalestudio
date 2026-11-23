import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChiOffQ

open Formalism.UG.P

section Cut

variable {F : Type} {iF : Field F} [NumberField F] {E : Type} {iE : Field E} [NumberField E]
  {iA : Algebra F E} {n : Type} [Fintype n] [DecidableEq n]

def cut1 (v : HeightOneSpectrum (𝓞 F)) :
    GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) →* GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  toFun x := afsplitU v 1 x
  map_one' := by
    apply Units.ext
    rw [afsplitU_coe, Units.val_one, Units.val_one, afsplitC_one]
  map_mul' x y := by
    rw [← afsplitU_mul, one_mul]

open Classical in
theorem glAdeleReplaceComponentByOne_component (v w : HeightOneSpectrum (𝓞 F)) (x : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) w) (cut1 v x) = if w = v then 1 else bc (prV (E := E) w) x := by
  by_cases h : w = v
  · subst h; rw [if_pos rfl]
    change bc (prV (E := E) w) (afsplitU w 1 x) = 1
    exact afsplit_right1 w 1 x
  · rw [if_neg h]
    apply Units.ext
    rw [afsplit_coe_bc_prV, afsplit_coe_bc_prV]
    exact afsplitC_prV_ne v w h _ _

def cutL (l : List (HeightOneSpectrum (𝓞 F))) :
    GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) →* GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  l.foldr (fun v f => (cut1 v).comp f) (MonoidHom.id _)

open Classical in
theorem cutL_prV (l : List (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F))
    (x : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) w) (cutL l x) = if w ∈ l then 1 else bc (prV (E := E) w) x := by
  induction l with
  | nil => simp [cutL, List.foldr_nil]
  | cons v l ih =>
    show bc (prV (E := E) w) (cut1 v (cutL l x)) = _
    rw [glAdeleReplaceComponentByOne_component, ih]
    by_cases h : w = v
    · simp [h]
    · simp [h]

theorem cutL_mem (σ : E →ₐ[F] E) (J : Matrix n n E) (l : List (HeightOneSpectrum (𝓞 F)))
    (x : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    cutL l x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  induction l with
  | nil => exact hx
  | cons v l ih => exact afsplitU_mem v σ J 1 _ (one_mem _) ih

theorem ext_bc (x y : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : ∀ w : HeightOneSpectrum (𝓞 F), bc (prV (E := E) w) x = bc (prV (E := E) w) y) : x = y := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [← sub_eq_zero]
  apply afsplit_inj
  intro w
  have e := congrArg (fun g : GL n (E ⊗[F] w.adicCompletion F) => g.val i j) (h w)
  change ((x : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).map (prV (E := E) w)) i j =
    ((y : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).map (prV (E := E) w)) i j at e
  rw [Matrix.map_apply, Matrix.map_apply] at e
  rw [map_sub, e, sub_self]

end Cut

section Re

theorem bc_reGL' {a b : ℕ} (h : a = b) {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : GL (Fin a) R) :
    bc φ (reGL h R g) = reGL h S (bc φ g) := by
  subst h
  apply Units.ext; ext x y; rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reGL_mem_UPts' {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin a) (E ⊗[F] R)) (hg : g ∈ UPts σ J R) :
    reGL h _ g ∈ UPts σ J' R := by
  subst h
  have e1 : J' = J := by ext x y; exact hJ x y
  have e2 : reGL (rfl : a = a) (E ⊗[F] R) g = g := by apply Units.ext; ext x y; rfl
  rw [e1, e2]; exact hg

theorem reGL_mem_levelVL {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin a → E))
    (g : GL (Fin a) (E ⊗[F] v.adicCompletion F)) (hg : g ∈ levelVL σ J v L) :
    reGL h _ g ∈ levelVL σ J' v (reL h L) := by
  subst h
  have e1 : J' = J := by ext x y; exact hJ x y
  have e2 : reGL (rfl : a = a) (E ⊗[F] v.adicCompletion F) g = g := by apply Units.ext; ext x y; rfl
  have e3 : reL (rfl : a = a) L = L := by
    have : ((reV (rfl : a = a) E : (Fin a → E) →ₗ[E] (Fin a → E)).restrictScalars (𝓞 E)) = LinearMap.id := by
      ext x i; rfl
    rw [reL, this, Submodule.map_id]
  rw [e1, e2, e3]; exact hg

end Re

end GlobalTheory.Mem.Col2.TC.ChiOffQ

namespace GlobalTheory.Mem.Col2.TC.ChiOffQ

theorem clause1_alg {M N : Type} [Group M] [Group N] {G : Subgroup M} {A : Subgroup N} (r : M ≃* N)
    (ρ : G →* G) (α chiJ : G →* ℂˣ) (φ : A →* ℂˣ) (κ : G) (κ' : A) (k1 : A)
    (hκ' : κ'.1 = r κ.1) (hk1 : k1.1 = r (ρ κ).1) (h1 : φ k1 = α κ)
    (hJ : ∀ (x : G) (k : A), k.1 = r x.1 → φ k = chiJ x) :
    φ κ' = (α * chiJ * (chiJ.comp ρ)⁻¹) κ := by
  have h2 : φ (k1⁻¹ * κ') = chiJ ((ρ κ)⁻¹ * κ) := hJ _ _ (by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hk1, hκ', Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv])
  calc φ κ' = φ (k1 * (k1⁻¹ * κ')) := by rw [mul_inv_cancel_left]
    _ = α κ * chiJ ((ρ κ)⁻¹ * κ) := by rw [map_mul, h1, h2]
    _ = (α * chiJ * (chiJ.comp ρ)⁻¹) κ := by
      rw [map_mul, map_inv, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply,
        mul_comm (chiJ (ρ κ))⁻¹, ← mul_assoc]

theorem clause2_alg {G B : Type} [Group G] [Group B] (ψ : G →* B) (ρ : G →* G) (χ1 : B →* ℂˣ) (chiJ : G →* ℂˣ)
    (κ : G) (κ' : B) (hρ : ρ κ = κ) (hψ : ψ κ = κ') : ((χ1.comp ψ) * chiJ * (chiJ.comp ρ)⁻¹) κ = χ1 κ' := by
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hρ, hψ,
    mul_inv_cancel_right]

end GlobalTheory.Mem.Col2.TC.ChiOffQ

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 20000000 in

theorem twLevJ_chi_off_of_lb : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → I.ReadsK l Z u a (B.R.m - 1) (Nat.sub_le _ _) chOf K → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ J : TwLevJ I l Z F Q u a chOf K, (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) J.levJ.Lb → ∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = χ κ) ∧ ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ' := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g hQ hStd hfr hRK hUloc hchi J hLb
  classical
  have hcutU : ∀ x : J.levJ.U, ChiOffQ.cutL Q.toList x.1 ∈ J.levJ.U := by
    intro x
    have hx := (J.levJ.U_eq x.1).1 x.2
    refine (J.levJ.U_eq _).2 ⟨ChiOffQ.cutL_mem _ _ _ _ hx.1, fun v => ?_⟩
    rw [ChiOffQ.cutL_prV]
    split_ifs
    · exact one_mem _
    · exact hx.2 v
  have hρex : ∃ ρ : J.levJ.U →* J.levJ.U, ∀ x, (ρ x).1 = ChiOffQ.cutL Q.toList x.1 :=
    ⟨MonoidHom.codRestrict ((ChiOffQ.cutL Q.toList).comp J.levJ.U.subtype) J.levJ.U hcutU, fun _ => rfl⟩
  obtain ⟨ρ, hρv⟩ := hρex
  have hFmem : ∀ x : J.levJ.U,
      reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ChiOffQ.cutL Q.toList x.1) ∈ (F u).levJ.U := by
    intro x
    have hx := (J.levJ.U_eq x.1).1 x.2
    have hUPx := ChiOffQ.reGL_mem_UPts' (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ _
      (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (fun _ _ => rfl) _ _ (((J.levJ.U_eq _).1 (hcutU x)).1)
    refine ((F u).levJ.U_eq _).2 ⟨hUPx, fun v => ?_⟩
    show bc (prV v) (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ChiOffQ.cutL Q.toList x.1)) ∈
      (F u).levJ.Uloc v
    rw [ChiOffQ.bc_reGL', ChiOffQ.cutL_prV]
    split_ifs with hv
    · rw [map_one]; exact one_mem _
    · have hvQ : v ∉ Q := fun h => hv (Finset.mem_toList.2 h)
      by_cases hb : v ∈ badG (I.rec7 l Z)
      · obtain ⟨j, hj⟩ : ∃ j : Fin 2, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
          rcases hb with h | h
          · exact ⟨0, h⟩
          · exact ⟨1, h⟩
        have hlevJ := J.levJ.Uloc_lev v (hx.2 v)
        have hlev : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV v) x.1) ∈
            levelVL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) v (F u).levJ.Lb := by
          rw [hLb]
          exact ChiOffQ.reGL_mem_levelVL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).sp.cm.sig
            ((I.rec7 l Z).sp.X (B.R.m - 1)).gram (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (fun _ _ => rfl)
            v J.levJ.Lb _ hlevJ
        obtain ⟨M, hMmem, hMeq⟩ := (J.J_g j v hj _ hlevJ).1 (hx.2 v)
        refine ((F u).glevJ.mem j v hj _ hlev).2 ⟨M, hMmem, ?_⟩
        rw [hMeq]
        rfl
      · exact (J.J_off v hvQ hb).le (Subgroup.mem_map_of_mem _ (hx.2 v))
  have hψex : ∃ ψ : J.levJ.U →* (F u).levJ.U, ∀ x,
      (ψ x).1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ChiOffQ.cutL Q.toList x.1) :=
    ⟨MonoidHom.codRestrict ((((reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom.comp
      (ChiOffQ.cutL Q.toList)).comp J.levJ.U.subtype)) (F u).levJ.U hFmem, fun _ => rfl⟩
  obtain ⟨ψ, hψv⟩ := hψex
  refine ⟨(F u).levJ.chi.comp ψ * J.chiJ * (J.chiJ.comp ρ)⁻¹, ?_, ?_⟩
  · intro β κ κ' hκ'
    have hK := ((K β).lev.U_eq κ'.1).1 κ'.2
    have hκ1v : (ρ κ).1 = ChiOffQ.cutL Q.toList κ.1 := hρv κ
    have hUP := ChiOffQ.reGL_mem_UPts' (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ _
      (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (fun _ _ => rfl) _ _ (((J.levJ.U_eq _).1 (ρ κ).2).1)
    have hloc : ∀ w, bc (prV w) (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ρ κ).1) =
        if w ∈ Q then 1 else bc (prV w) κ'.1 := by
      intro w
      rw [ChiOffQ.bc_reGL', hκ1v, ChiOffQ.cutL_prV, hκ', ChiOffQ.bc_reGL']
      simp only [Finset.mem_toList]
      split_ifs
      · exact map_one _
      · rfl
    have m1 : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ρ κ).1 ∈ (K β).lev.U :=
      ((K β).lev.U_eq _).2 ⟨hUP, fun w => by
        rw [hloc]
        split_ifs
        · exact one_mem _
        · exact hK.2 w⟩
    have m2 : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ρ κ).1 ∈
        ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U :=
      (((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U_eq _).2 ⟨hUP, fun w => by
        rw [hloc]
        split_ifs with hw
        · exact one_mem _
        · rw [← hUloc β w hw]; exact hK.2 w⟩
    have hk1ex : ∃ k1 : (K β).lev.U,
        k1.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (ρ κ).1 := ⟨⟨_, m1⟩, rfl⟩
    obtain ⟨k1, hk1⟩ := hk1ex
    have e3 : (K β).lev.chi k1 = (F u).levJ.chi (ψ κ) := by
      have m2' : k1.1 ∈ ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U := by rw [hk1]; exact m2
      rw [hchi β k1 ⟨k1.1, m2'⟩ rfl ?_]
      · exact (F u).levJ_chi h1 (g β) ⟨k1.1, m2'⟩ (ψ κ) (by rw [hψv, hk1, hκ1v])
      · intro v hv
        rw [hk1, hloc, if_pos hv]
    exact ChiOffQ.clause1_alg (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _) ρ ((F u).levJ.chi.comp ψ)
      J.chiJ (K β).lev.chi κ κ' k1 hκ' hk1 e3 (J.chiJ_eq β)
  · intro κ κ' hκ' hQκ
    have hc : ChiOffQ.cutL Q.toList κ.1 = κ.1 := ChiOffQ.ext_bc _ _ fun w => by
      rw [ChiOffQ.cutL_prV]
      split_ifs with hw
      · exact (hQκ w (Finset.mem_toList.1 hw)).symm
      · rfl
    have hρ : ρ κ = κ := Subtype.ext ((hρv κ).trans hc)
    have hψ : ψ κ = κ' := Subtype.ext (by rw [hψv, hc, hκ'])
    exact ChiOffQ.clause2_alg ψ ρ (F u).levJ.chi J.chiJ κ κ' hρ hψ

set_option maxHeartbeats 20000000 in

theorem twLevJ_chi_off : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → I.ReadsK l Z u a (B.R.m - 1) (Nat.sub_le _ _) chOf K → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → Nonempty Ch → ∀ J : TwLevJ I l Z F Q u a chOf K, ∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = χ κ) ∧ ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ' := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRK hUloc hchi hne J
  classical
  have hLb : (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) J.levJ.Lb := by
    obtain ⟨β⟩ := hne
    rw [← J.lb β, ← (F u).levJ_Lb h1 (g β)]
    obtain ⟨k, hk⟩ := hRK
    obtain ⟨k', hk'⟩ := (hStd u).mid (B.R.m - 1) h1 (succ_pred_m B.R)
    ext x
    exact (hk'.lb (g β) x).trans (hk.lb β x).symm
  exact twLevJ_chi_off_of_lb I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRK hUloc hchi J hLb

theorem stepBefore_cl_nonempty_tup {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (u : B.Word) (a : I.ι) :
    Nonempty (I.stp u a (B.R.m - 1)).Cl := by
  classical
  have hm2 := B.R.two_le_m
  have hmj : B.R.m - 1 + 1 = B.R.m := by omega
  haveI : NeZero (B.R.N (B.R.m - 1)) := ⟨(B.R.N_pos _).ne'⟩
  have hL := hOk.idx_ok a
  obtain ⟨b0x, -⟩ := hL.last_uniq
  let b0 : Idx I.sel (I.tup a) (I.idx a) (B.R.m - 1) := ⟨some (cast (by rw [show B.R.m - 1 = B.R.m - 2 + 1 by omega]) b0x), by simp; omega⟩
  let q0 : (I.stp u a (B.R.m - 1)).D b0 := ⟨(DecoF.base _ _ _ _ _, {z | z - 0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup a)) (DecoF.base B.fields.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))).deco.1.N
      (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst a).M : ℤ))}), by
    show _ ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) (B.R.m - 1)).ys _
    rw [ysAt_ys_of_eq _ _ _ hmj]
    exact ⟨0, zero_mem _, rfl⟩⟩
  exact ⟨(I.stp u a (B.R.m - 1)).cl b0 q0⟩

set_option maxHeartbeats 20000000 in

theorem twLevJ_exists_chi_off : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → I.ReadsK l Z u a (B.R.m - 1) (Nat.sub_le _ _) chOf K → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ J : TwLevJ I l Z F Q u a chOf K, ∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = χ κ) ∧ ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ' := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRK hUloc hchi J
  exact twLevJ_chi_off I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRK hUloc hchi
    ((stepBefore_cl_nonempty_tup I hI u a).map chOf) J

end GlobalTheory.Mem.Col2.TC
