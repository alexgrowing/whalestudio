import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalBasisRepLatticeIntegralCoordsSpecStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHermitianFormDescentCoefficientFieldStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWHlatIffStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWDelAtrIffStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co.PtInt

theorem natW_sgT {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (τ : B.fields.Tau) :
    ((I.perIn u a).sgT τ).natW = ((I.perIn u a).sg τ).natW := by
  funext i
  simp only [DomWeight.natW, PerIn.sgT, Col2.shW, DomWeight.detShift]
  split_ifs with h
  · congr 1
    ring
  · exact absurd i.2 (by omega)

theorem invTrK_bc {E K ι : Type} [Field E] [Field K] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (γ : GL (Fin n) E) :
    (fun τ => Formalism.UG.bc σ (invTrK (embGL emb γ) τ)) = invTrK (embGL (embAt σ emb) γ) := by
  funext τ
  ext a b
  have h1 := GlobalTheory.LvT.BuiltChain.invTrK_embGL_apply emb γ τ a b
  have h2 := GlobalTheory.LvT.BuiltChain.invTrK_embGL_apply (embAt σ emb) γ τ a b
  rw [h2]
  show σ (((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b) = _
  rw [h1]
  rfl

end GlobalTheory.PerQ.Co.PtInt

theorem GlobalTheory.PerQ.Co.PtInt.exists_mem_SP_of_coP_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ z ∈ ((I.tw l l0 Z).fm u a).ptC, (∀ c, GlobalTheory.PerQ.Co.coP I u a w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w ((I.rec7 l Z).fm u).sg) → ∃ y ∈ ((I.tw l l0 Z).fm u a).SP w, ((I.tw l l0 Z).fm u a).ptEmb y = z := by
  intro B X I hI l Z l0 u a w z hz hco
  have hOk : (I.perIn u a).S'.Ok := (l.per u a).step
  have hz' : z ∈ (I.perIn u a).S'.Fi B.fields.emb B.embLL (I.perIn u a).sgT := hz
  have key : ∀ c : (I.perIn u a).S'.Cl, ∃ v : Formalism.L2.DIV.VV B.fields.K (I.perIn u a).sgT,
      z c = evV B.fields.emb (1 : Matrix _ _ B.fields.E) (I.perIn u a).sgT B.embLL v ∧
      v ∈ locW B.places w (delAtr B.fields.emb (I.perIn u a).sgT ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c))) := by
    intro c
    obtain ⟨P, hP, hPz⟩ := (hz' c).1
    obtain ⟨G, hG, hGe⟩ := (GlobalTheory.LvT.Built.ValLat.mem_intSpan_iff (I.rec7 l Z) w _ (I.perIn u a).sgT
      (fun τ => (GlobalTheory.PerQ.Co.PtInt.natW_sgT I u a τ).symm) _).1 (hco c)
    have hGV : G ∈ Formalism.L2.DIV.VV B.fields.K (I.perIn u a).sgT := GlobalTheory.LvT.Built.ValLat.mem_VV_of_locP _ _ hG
    have hspec := GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c
    refine ⟨rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩, ?_, ?_⟩
    · rw [← hPz]
      show fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1 P =
        fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1
          (MvPolynomial.map B.embLL (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩).1)
      congr 1
      have e1 : (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩).1 =
          actP (I.perIn u a).sgT (invTrK (embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c))) G := rfl
      rw [e1]
      have e3 := GlobalTheory.LvT.Built.ValLat.map_actP B.embLL (I.perIn u a).sgT
        (invTrK (embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c))) G
      rw [GlobalTheory.PerQ.Co.PtInt.invTrK_bc] at e3
      refine Eq.trans ?_ e3.symm
      refine Eq.trans ?_ (congrArg (actP (I.perIn u a).sgT
        (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)))) hGe)
      show P = actP (I.perIn u a).sgT (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)))
        (actP (I.perIn u a).sgT (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹))
          (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT)
            (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (z c)))
      rw [← polyAction_mul, map_inv, map_inv, mul_inv_cancel, polyAction_one₂, ← hPz]
      have h := polOf_fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT)
        (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) P
      have e : (fun τ => ((fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
      rw [e] at h
      exact h.symm
    · have hinv : rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹
          (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩) = ⟨G, hGV⟩ := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [GlobalTheory.T.mem_locW_delAtr_iff' B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq (I.perIn u a).sgT
        (I.perIn u a).sg (GlobalTheory.PerQ.Co.PtInt.natW_sgT I u a) _ (hOk.lsh_lat c.1 _) w _ hspec.1, hinv]
      have h := hco c
      rw [hGe] at h
      exact h
  choose v hv1 hv2 using key
  obtain ⟨y, hy1, hy2⟩ := GlobalTheory.T.exists_hermitianForm_descent_coefficientField B.fields.emb B.embLL (I.perIn u a).S' (I.perIn u a).sgT (l.fmL u a).famP z hz' v hv1
  refine ⟨y, ?_, hy2⟩
  show y ∈ locW B.places w ((I.perIn u a).S'.hlat B.fields.emb (I.perIn u a).sgT (l.fmL u a).famP).L
  rw [GlobalTheory.T.mem_locW_hlat_iff' B.fields.emb B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq (I.perIn u a).S' (I.perIn u a).sgT
    (l.fmL u a).famP hOk w y]
  intro c
  rw [hy1 c]
  exact hv2 c
