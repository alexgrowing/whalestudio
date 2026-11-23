import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self homOfLinear fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.VB

namespace GlobalTheory.AffinePairingGlue

variable {T : Scheme.{0}} {H : T.Modules}

theorem exists_affine_le {V : T.Opens} {x : T} (hx : x ∈ V) :
    ∃ W : T.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ V := by
  obtain ⟨W, hW, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens hx
  exact ⟨W, hW, hxW, hWV⟩

theorem le_iSup_affine (V : T.Opens) :
    V ≤ ⨆ W : {W : T.Opens // IsAffineOpen W ∧ W ≤ V}, W.1 := fun x hx => by
  obtain ⟨W, hW, hxW, hWV⟩ := exists_affine_le hx
  exact Opens.mem_iSup.2 ⟨⟨W, hW, hWV⟩, hxW⟩

theorem fun_ext_affine {V : T.Opens} {a a' : Γ(T, V)}
    (e : ∀ (W : T.Opens) (_ : IsAffineOpen W) (h : W ≤ V), resG T h a = resG T h a') : a = a' :=
  fun_ext_of_cover (fun W : {W : T.Opens // IsAffineOpen W ∧ W ≤ V} => W.1) (fun W => W.2.2)
    (le_iSup_affine V) fun W => e W.1 W.2.1 W.2.2

variable (b : ∀ (V : T.Opens), IsAffineOpen V → (Γ(H, V) →ₗ[Γ(T, V)] Γ(H, V) →ₗ[Γ(T, V)] Γ(T, V)))
  (hb : ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (s t : Γ(H, V)), b V' hV' (resM H h s) (resM H h t) = resG T h (b V hV s t))

include hb in

theorem exists_glued (V : T.Opens) (s t : Γ(H, V)) : ∃ a : Γ(T, V),
    ∀ (W : T.Opens) (hW : IsAffineOpen W) (h : W ≤ V),
      resG T h a = b W hW (resM H h s) (resM H h t) := by
  obtain ⟨a, ha⟩ := exists_fun_of_cover (fun W : {W : T.Opens // IsAffineOpen W ∧ W ≤ V} => W.1)
    (fun W => W.2.2) (le_iSup_affine V)
    (fun W => b W.1 W.2.1 (resM H W.2.2 s) (resM H W.2.2 t)) fun k l =>
      fun_ext_affine fun W hW h => by
        rw [resG_resG, resG_resG, ← hb _ _ k.2.1 hW, ← hb _ _ l.2.1 hW]
        simp only [resM_resM]
  exact ⟨a, fun W hW h => ha ⟨W, hW, h⟩⟩

def glued (V : T.Opens) (s t : Γ(H, V)) : Γ(T, V) := (exists_glued b hb V s t).choose

theorem resG_glued {V W : T.Opens} (hW : IsAffineOpen W) (h : W ≤ V) (s t : Γ(H, V)) :
    resG T h (glued b hb V s t) = b W hW (resM H h s) (resM H h t) :=
  (exists_glued b hb V s t).choose_spec W hW h

theorem glued_affine {V : T.Opens} (hV : IsAffineOpen V) (s t : Γ(H, V)) :
    glued b hb V s t = b V hV s t := by
  have := resG_glued b hb hV le_rfl s t
  rwa [resG_self, resM_self, resM_self] at this

theorem glued_res {V W : T.Opens} (h : W ≤ V) (s t : Γ(H, V)) :
    glued b hb W (resM H h s) (resM H h t) = resG T h (glued b hb V s t) :=
  fun_ext_affine fun U hU h' => by
    rw [resG_resG, resG_glued b hb hU, resG_glued b hb hU, resM_resM, resM_resM]

def gluedBilin (V : T.Opens) : Γ(H, V) →ₗ[Γ(T, V)] Γ(H, V) →ₗ[Γ(T, V)] Γ(T, V) :=
  LinearMap.mk₂ Γ(T, V) (glued b hb V)
    (fun s s' t => fun_ext_affine fun U hU h => by
      simp only [map_add, resG_glued b hb hU, LinearMap.add_apply])
    (fun a s t => fun_ext_affine fun U hU h => by
      simp only [smul_eq_mul, map_mul, resG_glued b hb hU, resM_smul, map_smul,
        LinearMap.smul_apply])
    (fun s t t' => fun_ext_affine fun U hU h => by
      simp only [map_add, resG_glued b hb hU])
    (fun a s t => fun_ext_affine fun U hU h => by
      simp only [smul_eq_mul, map_mul, resG_glued b hb hU, resM_smul, map_smul])

def toDual : H ⟶ dual H :=
  homOfLinear (fun V =>
    { toFun s := dualMk (fun W h => gluedBilin b hb W (resM H h s))
        fun W W' h h' t => by
          change glued b hb W' _ _ = resG T h' (glued b hb W _ _)
          rw [← glued_res, resM_resM]
      map_add' := fun s t => dual_ext fun W h u => by
        change gluedBilin b hb W (resM H h (s + t)) u = _
        rw [map_add, map_add]; rfl
      map_smul' := fun a s => dual_ext fun W h u => by
        change gluedBilin b hb W (resM H h (a • s)) u = _
        rw [resM_smul, map_smul]; rfl })
    fun h s => dual_ext fun W h' u =>
      congrArg (fun z => glued b hb W z u) (resM_resM h h' s)

theorem dualApp_toDual {V W : T.Opens} (h : W ≤ V) (s : Γ(H, V)) (t : Γ(H, W)) :
    dualApp ((toDual b hb).app V s) h t = glued b hb W (resM H h s) t := rfl

theorem dualApp_toDual_affine {V : T.Opens} (hV : IsAffineOpen V) (s t : Γ(H, V)) :
    dualApp ((toDual b hb).app V s) le_rfl t = b V hV s t := by
  rw [dualApp_toDual, resM_self, glued_affine]

theorem bijective_toDual_app {r : ℕ} {U V : T.Opens} {e : Fin r → Γ(H, U)} (he : IsFrame e)
    (h : V ≤ U) (hV : IsAffineOpen V) (hp : (b V hV).IsPerfPair) :
    Function.Bijective ((toDual b hb).app V) := by
  refine ⟨fun s s' hs => hp.bijective_left.1 (LinearMap.ext fun t => ?_), fun l => ?_⟩
  · rw [← dualApp_toDual_affine b hb hV, ← dualApp_toDual_affine b hb hV, hs]
  · obtain ⟨s, hs⟩ := hp.bijective_left.2 (dualApp l le_rfl)
    exact ⟨s, he.dual_ext h fun i => by rw [dualApp_toDual_affine b hb hV, hs]⟩

theorem isIso_toDual {r : ℕ} (hH : IsVB H r)
    (hp : ∀ (V : T.Opens) (hV : IsAffineOpen V), (b V hV).IsPerfPair) : IsIso (toDual b hb) := by
  have key (W : T.Opens) (x : T) (hx : x ∈ W) : ∃ V : T.Opens, x ∈ V ∧ V ≤ W ∧
      Function.Bijective ((toDual b hb).app V) := by
    obtain ⟨U, e, hxU, he⟩ := hH x
    obtain ⟨V, hV, hxV, hle⟩ := exists_affine_le (V := W ⊓ U) ⟨hx, hxU⟩
    exact ⟨V, hxV, hle.trans inf_le_left,
      bijective_toDual_app b hb he (hle.trans inf_le_right) hV (hp V hV)⟩
  have : Mono (toDual b hb) := QCoh.mono_of_locally_app_injective _ fun W x hx =>
    have ⟨V, h₁, h₂, h₃⟩ := key W x hx
    ⟨V, h₁, h₂, h₃.1⟩
  have : Epi (toDual b hb) := QCoh.epi_of_locally_app_surjective _ fun W x hx =>
    have ⟨V, h₁, h₂, h₃⟩ := key W x hx
    ⟨V, h₁, h₂, h₃.2⟩
  exact isIso_of_mono_of_epi _

theorem comp_toDual_comp_dualMap {F : T.Modules} (i : F ⟶ H)
    (hi : ∀ (V : T.Opens) (hV : IsAffineOpen V) (x y : Γ(F, V)),
      b V hV (i.app V x) (i.app V y) = 0) : i ≫ toDual b hb ≫ dualMap i = 0 := by
  ext V x : 3
  refine dual_ext fun W h y => fun_ext_affine fun U hU h' => ?_
  change resG T h' (glued b hb W (resM H h (i.app V x)) (i.app W y)) = resG T h' 0
  rw [resG_glued b hb hU, resM_resM, ← app_resM, ← app_resM, hi, map_zero]

theorem exists_iso_dual_of_affine_pairing :
    ∀ (T : Scheme.{0}) (H : T.Modules) (r : ℕ), GlobalTheory.VB.IsVB H r →
    ∀ (b : ∀ (V : T.Opens), IsAffineOpen V → (Γ(H, V) →ₗ[Γ(T, V)] Γ(H, V) →ₗ[Γ(T, V)] Γ(T, V))),
      (∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) (s t : Γ(H, V)),
          b V' hV' (GlobalTheory.Twist.resM H h s) (GlobalTheory.Twist.resM H h t) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG T h (b V hV s t)) →
      (∀ (V : T.Opens) (hV : IsAffineOpen V), (b V hV).IsPerfPair) →
      ∀ (F : T.Modules) (i : F ⟶ H),
        (∀ (V : T.Opens) (hV : IsAffineOpen V) (x y : Γ(F, V)), b V hV (i.app V x) (i.app V y) = 0) →
        ∃ β : H ⟶ GlobalTheory.VB.dual H, IsIso β ∧ i ≫ β ≫ GlobalTheory.VB.dualMap i = 0 ∧
          ∀ (V : T.Opens) (hV : IsAffineOpen V) (s t : Γ(H, V)), GlobalTheory.VB.dualApp (β.app V s) le_rfl t = b V hV s t :=
  fun _ _ _ hH b hb hp _ i hi =>
    ⟨toDual b hb, isIso_toDual b hb hH hp, comp_toDual_comp_dualMap b hb i hi,
      fun _ hV s t => dualApp_toDual_affine b hb hV s t⟩

end GlobalTheory.AffinePairingGlue
