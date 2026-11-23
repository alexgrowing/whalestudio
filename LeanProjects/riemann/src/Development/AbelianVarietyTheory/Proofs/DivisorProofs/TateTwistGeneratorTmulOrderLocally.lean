import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionwiseTensorPresheafLocallyBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistModuleFreeAndGeneratorSummand

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwMulOrder

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : Scheme.{0} → Prop} (h : Loc U P)
    (hPQ : ∀ V (g : V ⟶ U), P V g → Loc V fun W _ => Q W) : Loc U fun W _ => Q W := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hQ using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => hPQ V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun ⦃V⦄ ⦃g⦄ hg => T V g hg), ?_, ?_⟩
  · exact GrothendieckTopology.bind_covering _ hS (fun ⦃V⦄ ⦃g⦄ hg => hT V g hg)
  · rintro W _ ⟨V, k, g, hg, hk, -⟩
    exact hQ V g hg W k hk

def pgen (q : ℕ) (i : ℤ) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) : (Scheme.Γ ⋙ twF q i).obj (op V) :=
  Submodule.Quotient.mk (Finsupp.single ζ 1)

theorem pgen_map (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    ((Scheme.Γ ⋙ twF q i).map g.op).hom (pgen q i ζ) = pgen q i (ζ.map g.appTop.hom) := by
  show Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (q := q) g.appTop.hom) (Finsupp.single ζ 1)) =
    (Submodule.Quotient.mk (Finsupp.single (ζ.map g.appTop.hom) 1) :
      (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(V, ⊤))
  rw [Finsupp.mapDomain_single]

theorem twGen_eq (q : ℕ) (i : ℤ) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) :
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom (pgen q i ζ) = twGen i ζ := rfl

theorem twGen_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    ((tw q i).obj.map g.op).hom (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  have h := congrArg (fun f => f.hom (pgen q i ζ))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [pgen_map] at h
  rw [← twGen_eq, ← twGen_eq]
  exact h.symm

theorem step_point (q : ℕ) [NeZero q] (i j : ℤ) (V : Scheme.{0}) [Nonempty V] (ζ : Prim q Γ(V, ⊤)) (c : ℕ)
    (h : c • (pgen q j ζ ⊗ₜ[ULift.{1} (ZMod q)] pgen q i ζ) = 0) : q ∣ c := by
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨Classical.arbitrary V, trivial⟩⟩
  haveI : Nontrivial Γ(V, ⊤) := Scheme.component_nontrivial V ⊤
  obtain ⟨fj, hfj⟩ := (GlobalTheory.TwFree.twist_free q j Γ(V, ⊤)).2 ζ
  obtain ⟨fi, hfi⟩ := (GlobalTheory.TwFree.twist_free q i Γ(V, ⊤)).2 ζ
  let fj' : (Scheme.Γ ⋙ twF q j).obj (op V) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) := fj
  let fi' : (Scheme.Γ ⋙ twF q i).obj (op V) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) := fi
  have e1 : fj' (pgen q j ζ) = 1 := hfj
  have e2 : fi' (pgen q i ζ) = 1 := hfi
  have h2 : (TensorProduct.lid (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)))
      (TensorProduct.map fj' fi' (c • (pgen q j ζ ⊗ₜ[ULift.{1} (ZMod q)] pgen q i ζ))) = 0 := by
    rw [h, map_zero, map_zero]
  rw [map_nsmul, map_nsmul, TensorProduct.map_tmul, e1, e2, TensorProduct.lid_tmul, one_smul] at h2
  have h3 : ((c : ZMod q)) = 0 := by
    have := congrArg ULift.down h2
    simpa using this
  exact (ZMod.natCast_eq_zero_iff c q).1 h3

theorem step_swap (q : ℕ) [NeZero q] (i j : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (c : ℕ)
    (h : c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] pgen q j ζ) = 0) : Loc V fun W _ => Nonempty W → q ∣ c := by
  have hφ := toSheafify_loc_bij_lift (ZMod q) (Scheme.Γ ⋙ twF q i)
  have key := (tensor_loc_bij (ZMod q) (Scheme.Γ ⋙ twF q j) (Scheme.Γ ⋙ twF q i) _
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) hφ.1 hφ.2.1 V).2
    (c • (pgen q j ζ ⊗ₜ pgen q i ζ)) (by
      rw [map_nsmul, LinearMap.lTensor_tmul, twGen_eq]
      have := congrArg (TensorProduct.comm _ _ _) h
      rwa [map_nsmul, TensorProduct.comm_tmul, map_zero] at this)
  refine loc_mono key ?_
  intro W g hg hW
  rw [map_nsmul, TensorProduct.map_tmul, pgen_map, pgen_map] at hg
  exact step_point q i j W (ζ.map g.appTop.hom) c hg

theorem tw_mul_order : ∀ (q : ℕ) [NeZero q] (i j : ℤ) (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ),
    c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ) = 0 → Loc W fun V _ => Nonempty V → q ∣ c := by
  intro q _ i j W ζ c h
  have hφ := toSheafify_loc_bij_lift (ZMod q) (Scheme.Γ ⋙ twF q j)
  have key := (tensor_loc_bij (ZMod q) (tw q i).obj (Scheme.Γ ⋙ twF q j) _
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q j)) hφ.1 hφ.2.1 W).2
    (c • (twGen i ζ ⊗ₜ pgen q j ζ)) (by rw [map_nsmul, LinearMap.lTensor_tmul, twGen_eq]; exact h)
  refine loc_bind key fun V g hg => step_swap q i j V (ζ.map g.appTop.hom) c ?_
  rw [map_nsmul, TensorProduct.map_tmul, pgen_map, twGen_res] at hg
  exact hg

end GlobalTheory.TwMulOrder

end
