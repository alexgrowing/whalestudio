import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenDecompositionVectorBundle
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SubGlue
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.LB (resG_resG resG_self exists_fun_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)

variable {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {L : LB X}

abbrev spanRes (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (k : L.ι) {W : X.Opens} (hk : W ≤ L.U k) :
    Submodule Γ(X, W) Γ(F, W) :=
  Submodule.span Γ(X, W) (Set.range fun i => resM F hk (s k i))

theorem resM_mem_spanRes (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) {k : L.ι} {W W' : X.Opens}
    (hW : W' ≤ W) (hk : W ≤ L.U k) {x : Γ(F, W)} (hx : x ∈ spanRes s k hk) :
    resM F hW x ∈ spanRes s k (hW.trans hk) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => resG X hW (c i), ?_⟩
  simp only [map_sum, resM_smul, resM_resM]

theorem spanRes_le (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (A : ∀ k k' : L.ι, Matrix (Fin r) (Fin r) Γ(X, L.U k ⊓ L.U k'))
    (hA : ∀ (k k' : L.ι) (i : Fin r), resM F (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (s k' i) =
      ∑ j, A k k' j i • resM F (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k) (s k j))
    (k k' : L.ι) {W : X.Opens} (hk : W ≤ L.U k) (hk' : W ≤ L.U k') :
    spanRes s k' hk' ≤ spanRes s k hk := by
  rw [spanRes, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have e := congrArg (resM F (le_inf hk hk')) (hA k k' i)
  simp only [resM_resM, map_sum, resM_smul] at e
  change resM F hk' (s k' i) ∈ spanRes s k hk
  rw [show resM F hk' (s k' i) = _ from e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

def IsLoc (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (V : X.Opens) (x : Γ(F, V)) : Prop :=
  ∀ p ∈ V, ∃ (k : L.ι) (W : X.Opens) (h : W ≤ V) (hk : W ≤ L.U k), p ∈ W ∧
    resM F h x ∈ spanRes s k hk

def sub (hL : L.IsLB) (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (hmono : ∀ (k k' : L.ι) (W : X.Opens) (hk : W ≤ L.U k) (hk' : W ≤ L.U k'),
      spanRes s k' hk' ≤ spanRes s k hk) : VB.Sub F where
  sec V :=
    { carrier := {x | IsLoc s V x}
      zero_mem' := fun p hp => by
        obtain ⟨k, hk⟩ := Semi.LB.mem_of_cover hL p
        exact ⟨k, V ⊓ L.U k, inf_le_left, inf_le_right, ⟨hp, hk⟩, by rw [map_zero]; exact zero_mem _⟩
      add_mem' := fun {x y} hx hy p hp => by
        obtain ⟨k, W, h, hk, hpW, hxW⟩ := hx p hp
        obtain ⟨k', W', h', hk', hpW', hyW'⟩ := hy p hp
        refine ⟨k, W ⊓ W', inf_le_left.trans h, inf_le_left.trans hk, ⟨hpW, hpW'⟩, ?_⟩
        rw [map_add]
        refine add_mem ?_ (hmono k k' _ (inf_le_left.trans hk) (inf_le_right.trans hk') ?_)
        · have := resM_mem_spanRes s (inf_le_left : W ⊓ W' ≤ W) hk hxW
          rw [resM_resM] at this
          exact this
        · have := resM_mem_spanRes s (inf_le_right : W ⊓ W' ≤ W') hk' hyW'
          rw [resM_resM] at this
          exact this
      smul_mem' := fun a x hx p hp => by
        obtain ⟨k, W, h, hk, hpW, hxW⟩ := hx p hp
        refine ⟨k, W, h, hk, hpW, ?_⟩
        rw [resM_smul]
        exact Submodule.smul_mem _ _ hxW }
  res_mem {V W} hWV x hx := fun p hp => by
    obtain ⟨k, W', h', hk, hp', hx'⟩ := (hx : IsLoc s V x) p (hWV hp)
    refine ⟨k, W ⊓ W', inf_le_left, inf_le_right.trans hk, ⟨hp, hp'⟩, ?_⟩
    rw [resM_resM]
    have := resM_mem_spanRes s (inf_le_right : W ⊓ W' ≤ W') hk hx'
    rw [resM_resM] at this
    exact this
  mem_of_local {V x} H := fun p hp => by
    obtain ⟨W, h, hpW, hW⟩ := H p hp
    obtain ⟨k, W', h', hk, hp', hx'⟩ := (hW : IsLoc s W _) p hpW
    refine ⟨k, W', h'.trans h, hk, hp', ?_⟩
    rw [resM_resM] at hx'
    exact hx'

theorem mem_spanRes_of_mem (hL : L.IsLB) (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (hmono : ∀ (k k' : L.ι) (W : X.Opens) (hk : W ≤ L.U k) (hk' : W ≤ L.U k'),
      spanRes s k' hk' ≤ spanRes s k hk)
    (hli : ∀ (k : L.ι) (V : X.Opens) (h : V ≤ L.U k),
      LinearIndependent Γ(X, V) fun i => resM F h (s k i))
    {k : L.ι} {V : X.Opens} (hV : V ≤ L.U k) {x : Γ(F, V)}
    (hx : x ∈ (sub hL s hmono).sec V) : x ∈ spanRes s k hV := by
  have hx' : IsLoc s V x := hx
  choose k' W hW hk' hpW hxW using fun p : V => hx' p p.2
  have hc : V ≤ iSup W := fun p hp => Opens.mem_iSup.2 ⟨⟨p, hp⟩, hpW _⟩
  have hin (p : V) : resM F (hW p) x ∈ spanRes s k ((hW p).trans hV) :=
    hmono k (k' p) _ _ _ (hxW p)
  choose c hc' using fun p => (Submodule.mem_span_range_iff_exists_fun _).1 (hin p)
  have key (p q : V) (i : Fin r) : resG X (inf_le_left : W p ⊓ W q ≤ W p) (c p i) =
      resG X (inf_le_right : W p ⊓ W q ≤ W q) (c q i) := by
    have hl := hli k (W p ⊓ W q) (inf_le_left.trans ((hW p).trans hV))
    have e1 := congrArg (resM F (inf_le_left : W p ⊓ W q ≤ W p)) (hc' p)
    have e2 := congrArg (resM F (inf_le_right : W p ⊓ W q ≤ W q)) (hc' q)
    simp only [map_sum, resM_smul, resM_resM] at e1 e2
    exact Fintype.linearIndependent_iffₛ.1 hl _ _ (e1.trans e2.symm) i
  choose b hb using fun i => exists_fun_of_cover W hW hc (fun p => c p i) fun p q => key p q i
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨b, ?_⟩
  refine sec_ext_of_cover W hW hc fun p => ?_
  simp only [map_sum, resM_smul, resM_resM, hb]
  exact hc' p

end GlobalTheory.SubGlue

namespace GlobalTheory.SubGlue
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)

theorem exists_sub_isVB_lbIso_det : ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ) (L : LB X), L.IsLB → ∀ (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (A : ∀ k k' : L.ι, Matrix (Fin r) (Fin r) Γ(X, L.U k ⊓ L.U k')), (∀ (k : L.ι) (V : X.Opens) (h : V ≤ L.U k), LinearIndependent Γ(X, V) fun i => GlobalTheory.Twist.resM F h (s k i)) → (∀ (k k' : L.ι) (i : Fin r), GlobalTheory.Twist.resM F (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (s k' i) = ∑ j, A k k' j i • GlobalTheory.Twist.resM F (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k) (s k j)) → (∀ k k' : L.ι, (L.g k k').val = (A k k').det) → ∃ (W : X.Modules) (ι : W ⟶ F), Mono ι ∧ GlobalTheory.VB.IsVB W r ∧ LBIso L (GlobalTheory.VB.det W r) := by
  intro X F r L hL s A hli hA hdet
  have hmono := spanRes_le s A hA
  let N := sub hL s hmono
  have hmem (k : L.ι) (i : Fin r) : s k i ∈ N.sec (L.U k) := fun p hp =>
    ⟨k, L.U k, le_rfl, le_rfl, hp, Submodule.subset_span ⟨i, rfl⟩⟩
  have hfr (k : L.ι) : VB.IsFrame fun i => N.mkSec (s k i) (hmem k i) :=
    GlobalTheory.EigenFrames.isFrame_mkSec N (s k) (hmem k) (hli k)
      fun V h x hx => mem_spanRes_of_mem hL s hmono hli h hx
  have hv (k k' : L.ι) (i : Fin r) :
      resM N.toMod (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (N.mkSec (s k' i) (hmem k' i)) =
        ((hfr k).basis (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k)).equivFun.symm
          fun j => A k k' j i := by
    rw [VB.IsFrame.basis_equivFun_symm]
    apply N.incl_app_injective
    rw [app_resM, VB.Sub.incl_app_mkSec, hA]
    rw [← appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, appLinear_apply, app_resM, VB.Sub.incl_app_mkSec]
  refine ⟨N.toMod, N.incl, inferInstance, ?_⟩
  refine VB.lbIso_det_of_frames hL _ hfr fun k k' => Units.ext ?_
  rw [hdet, VB.IsFrame.val_detUnit, Module.Basis.det_apply]
  congr 1
  ext a b
  rw [Module.Basis.toMatrix_apply, hv, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.SubGlue
