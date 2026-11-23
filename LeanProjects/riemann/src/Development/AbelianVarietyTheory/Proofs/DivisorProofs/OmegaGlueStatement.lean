import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.VB

namespace GlobalTheory.OmegaHT.FrameGlue

variable {X : Scheme.{0}} {F : X.Modules} {r : ℕ}

abbrev spanOn {V : X.Opens} (η : Fin r → Γ(F, V)) {U : X.Opens} (h : U ≤ V) : Submodule Γ(X, U) Γ(F, U) :=
  Submodule.span Γ(X, U) (Set.range fun l => resM F h (η l))

theorem resM_mem_spanOn {V U W : X.Opens} (η : Fin r → Γ(F, V)) (h : U ≤ V) (h' : W ≤ U) {s : Γ(F, U)}
    (hs : s ∈ spanOn η h) : resM F h' s ∈ spanOn η (h'.trans h) := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hs
  simp only [map_sum, resM_smul, resM_resM]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

def locSpan {V : X.Opens} (η : Fin r → Γ(F, V)) : Sub F where
  sec U :=
    { carrier := {s | ∀ z : X, z ∈ U → z ∈ V → ∃ (W : X.Opens) (h : W ≤ U) (h' : W ≤ V), z ∈ W ∧
        resM F h s ∈ spanOn η h'}
      add_mem' := fun {s t} hs ht z hz hz' => by
        obtain ⟨W, h, h', hW, k⟩ := hs z hz hz'
        obtain ⟨W', g, g', hW', k'⟩ := ht z hz hz'
        refine ⟨W ⊓ W', inf_le_left.trans h, inf_le_left.trans h', ⟨hW, hW'⟩, ?_⟩
        rw [map_add]
        refine add_mem ?_ ?_
        · simpa only [resM_resM] using resM_mem_spanOn η h' (inf_le_left : W ⊓ W' ≤ W) k
        · simpa only [resM_resM] using resM_mem_spanOn η g' (inf_le_right : W ⊓ W' ≤ W') k'
      zero_mem' := fun z hz hz' =>
        ⟨U ⊓ V, inf_le_left, inf_le_right, ⟨hz, hz'⟩, by rw [map_zero]; exact zero_mem _⟩
      smul_mem' := fun a s hs z hz hz' => by
        obtain ⟨W, h, h', hW, k⟩ := hs z hz hz'
        refine ⟨W, h, h', hW, ?_⟩
        rw [resM_smul]
        exact Submodule.smul_mem _ _ k }
  res_mem {U U'} g s hs z hz hz' := by
    obtain ⟨W, h, h', hW, k⟩ := hs z (g hz) hz'
    refine ⟨W ⊓ U', inf_le_right, inf_le_left.trans h', ⟨hW, hz⟩, ?_⟩
    simpa only [resM_resM] using resM_mem_spanOn η h' (inf_le_left : W ⊓ U' ≤ W) k
  mem_of_local {U s} H z hz hz' := by
    obtain ⟨W, h, hW, hs⟩ := H z hz
    obtain ⟨W', g, g', hW', k⟩ := hs z hW hz'
    exact ⟨W', g.trans h, g', hW', by simpa only [resM_resM] using k⟩

theorem mem_locSpan {V V' : X.Opens} {η : Fin r → Γ(F, V)} {η' : Fin r → Γ(F, V')} (h : LocInSpan η η') (j : Fin r) :
    η' j ∈ (locSpan η).sec V' := fun z hz' hz =>
  have ⟨U, g, g', hU, k⟩ := h z hz hz'
  ⟨U, g', g, hU, k j⟩

theorem isFrame_mkSec (N : Sub F) {V : X.Opens} {η : Fin r → Γ(F, V)} (hη : ∀ l, η l ∈ N.sec V)
    (hi : ∀ (U : X.Opens) (h : U ≤ V), LinearIndependent Γ(X, U) fun l => resM F h (η l))
    (hN : ∀ U, N.sec U ≤ (locSpan η).sec U) : IsFrame fun l => N.mkSec (η l) (hη l) := by
  have key (U : X.Opens) (h : U ≤ V) (a : Fin r → Γ(X, U)) :
      N.incl.app U (Fintype.linearCombination Γ(X, U) (fun l => resM N.toMod h (N.mkSec (η l) (hη l))) a) =
        Fintype.linearCombination Γ(X, U) (fun l => resM F h (η l)) a := by
    simp only [Fintype.linearCombination_apply, map_sum, Scheme.Modules.Hom.app_smul, app_resM, Sub.incl_app_mkSec]
  have inj (U : X.Opens) (h : U ≤ V) : Function.Injective
      (Fintype.linearCombination Γ(X, U) fun l => resM N.toMod h (N.mkSec (η l) (hη l))) := fun a b hab => by
    have := congrArg (N.incl.app U) hab
    rw [key, key] at this
    exact (hi U h).fintypeLinearCombination_injective this
  intro U h
  refine ⟨inj U h, fun s => ?_⟩
  have hs := hN U (N.incl_app_mem s)
  choose W hW hW' hx hb using fun x : U => hs x x.2 (h x.2)
  have hc : U ≤ iSup W := fun x hxU => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx _⟩
  choose a ha using fun x => (Submodule.mem_span_range_iff_exists_fun _).1 (hb x)
  have ha' (x : U) : Fintype.linearCombination Γ(X, W x)
      (fun l => resM N.toMod ((hW x).trans h) (N.mkSec (η l) (hη l))) (a x) = resM N.toMod (hW x) s := by
    apply N.incl_app_injective
    rw [key, app_resM, ← ha x, Fintype.linearCombination_apply]
  have agree (x y : U) : (fun i => resG X (inf_le_left : W x ⊓ W y ≤ W x) (a x i)) =
      fun i => resG X (inf_le_right : W x ⊓ W y ≤ W y) (a y i) := by
    apply inj _ (inf_le_left.trans ((hW x).trans h))
    rw [← resM_linearCombination _ ((hW x).trans h), ← resM_linearCombination _ ((hW y).trans h),
      ha', ha', resM_resM, resM_resM]
  choose b hb' using fun i => GlobalTheory.LB.exists_fun_of_cover W hW hc (fun x => a x i)
    fun x y => congrFun (agree x y) i
  refine ⟨b, GlobalTheory.Twist.sec_ext_of_cover W hW hc fun x => ?_⟩
  rw [resM_linearCombination, ← ha' x]
  exact congrArg _ (funext fun i => hb' i x)

theorem glue : GlueSt := by
  intro X F r J V η hc hi hs
  let N : Sub F := Sub.iInf fun α => locSpan (η α)
  have hη (α : J) (l : Fin r) : η α l ∈ N.sec (V α) :=
    (Submodule.mem_iInf _).2 fun β => mem_locSpan (hs β α) l
  have hf (α : J) : IsFrame fun l => N.mkSec (η α l) (hη α l) :=
    isFrame_mkSec N (hη α) (hi α) fun U => iInf_le (fun β => (locSpan (η β)).sec U) α
  refine ⟨N.toMod, N.incl, fun z => ?_, fun α => ⟨_, hf α, fun l => rfl⟩⟩
  obtain ⟨α, hα⟩ := hc z
  exact ⟨V α, _, hα, hf α⟩

end GlobalTheory.OmegaHT.FrameGlue
