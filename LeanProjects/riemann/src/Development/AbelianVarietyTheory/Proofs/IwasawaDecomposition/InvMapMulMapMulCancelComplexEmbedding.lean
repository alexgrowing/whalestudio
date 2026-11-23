import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.TC.inv_map_mul_map_mul_cancel_complex_embedding {n : ℕ} {E : Type} [Field E] (f : E →+* ℂ) (γ : GL (Fin n) E) (M : Matrix (Fin n) (Fin n) ℂ) :
    ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map f * ((γ : Matrix (Fin n) (Fin n) E).map f * M) = M := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul]
  simp

theorem GlobalTheory.Mem.Col2.TC.tr_eq_of_isTr : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY → ∀ (b : (I.stp u a i).β) (g : (I.stp u a i).G b) (h : (I.chain l u a).Y i → ℂ) (s s' : (I.chain l u a).Y i), IsTr (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) ((I.stp u a i).gam b g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E)) (eY s') (eY s) → (I.stp u a i).tr B.fields.emb B.embLL b g h s = B.embLL (((I.stp u a i).chr b g : B.LLˣ) : B.LL) * h s' := by
  intro B X I _ _ l Z u a i hi eY hId b g h s s' hT
  have key : s' = frMul B.fields.emb B.embLL ((I.stp u a i).gam b g)⁻¹ s := by
    apply Subtype.ext
    funext τ
    have h1 : s.1 τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z))
        (((I.stp u a i).gam b g : GL (Fin (B.R.N i)) B.fields.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E) τ * s'.1 τ := by
      have := hT τ
      rw [hId, hId] at this
      exact this
    have hf : embAt B.embLL B.fields.emb τ = Formalism.L2.Forms.embT (I.rec7 l Z) τ := B.fields_embC τ
    show s'.1 τ = ((((I.stp u a i).gam b g)⁻¹ : GL _ _) : Matrix _ _ _).map (embAt B.embLL B.fields.emb τ) * s.1 τ
    rw [h1, hf]
    exact (GlobalTheory.Mem.Col2.TC.inv_map_mul_map_mul_cancel_complex_embedding _ _ _).symm
  show B.embLL _ * h (frMul B.fields.emb B.embLL ((I.stp u a i).gam b g)⁻¹ s) = _
  rw [← key]
