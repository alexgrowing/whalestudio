import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOfEntries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EmbTopBlock

theorem iXm_entry {D : D7}
    (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
      D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b)
    (i : Fin (D.R.N D.R.m)) (b : Fin (D.R.N D.R.m - 1)) :
    iXm D i b = if (i : ℕ) = b then 1 else 0 := by
  have hP' : D.sp.X'.rank = D.R.N D.R.m - 1 := rankP D
  have hN' : (D.sp.X D.R.m).rank = D.R.N D.R.m := rankN D D.R.m le_rfl
  have hb : (b : ℕ) < D.sp.X'.rank := by have := b.2; omega
  have hb2 : (b : ℕ) < (D.sp.X D.R.m).rank := by have := b.2; omega
  have key : D.sp.iX' (D.sp.X'.frame ⟨b, hb⟩) = (D.sp.X D.R.m).frame ⟨b, hb2⟩ := hi _ _ rfl
  rw [iXm, LinearMap.toMatrix'_apply, iXc]
  have hs : (D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm
      (Pi.single b 1) = D.sp.X'.frame ⟨b, hb⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    ext j
    simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
      Pi.single_apply, Finsupp.single_apply, Fin.ext_iff, Fin.val_cast, finCongr_symm, finCongr_apply, Fin.coe_cast, LinearMap.funLeft_apply, Function.comp_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hs, key]
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
      Pi.single_apply, Finsupp.single_apply, Fin.ext_iff, Fin.val_cast, finCongr_symm, finCongr_apply, Fin.coe_cast, LinearMap.funLeft_apply, Function.comp_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

end GlobalTheory.EmbTopBlock

namespace GlobalTheory.EmbTopBlock

theorem piT_coe_ne_zero {B : GlobalTheory.Mem.Base} (X : PreX B.toPre) (u : B.Word) : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := by
  intro h0
  have hn := X.piT_norm u
  rw [h0, zero_mul] at hn
  have hT : B.T u = 0 := by exact_mod_cast hn.symm
  have h1 := X.T_gt u
  have h2 := X.a_gt
  rw [hT] at h1
  have h3 := h2.trans h1
  exact (Nat.not_lt_zero _) (by exact_mod_cast h3)

theorem isBlock_infM_emb : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (θ : InfFam (I.rec7 l Z)), IsInfFam θ → ∀ (emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m)) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) emb → ∀ (k : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (τ : (I.rec7 l Z).what₂.Tau), GlobalTheory.BranchFormula.IsBlock hN (infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb k) τ) (infM θ _ (rankP (I.rec7 l Z)) k τ) 1 := by
  intro B X I _hOk hP l Z u θ _hθ emb hN hemb k τ
  obtain ⟨h1, h2⟩ := hemb k
  let q : AE (I.rec7 l Z) →+* ℂ := (θ τ).comp (infPart (I.rec7 l Z))
  let p : (I.rec7 l Z).host.E →+* ℂ := q.comp (incA (I.rec7 l Z))
  let G : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ := infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb k) τ
  let G' : Matrix (Fin (B.R.N B.R.m - 1)) (Fin (B.R.N B.R.m - 1)) ℂ := infM θ _ (rankP (I.rec7 l Z)) k τ
  let J : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m - 1)) ℂ := (iXm (I.rec7 l Z)).map p
  have hF : J = Matrix.of (fun (i : Fin (B.R.N B.R.m)) (a : Fin (B.R.N B.R.m - 1)) => if (i : ℕ) = a then (1 : ℂ) else 0) := by
    ext i a
    show p (iXm (I.rec7 l Z) i a) = if (i : ℕ) = a then (1 : ℂ) else 0
    rw [iXm_entry (D := I.rec7 l Z) hP.iX i a]
    split_ifs <;> simp
  have e1 : G * J = J * G' := by
    have := congrArg (fun M => Matrix.map M q) h1
    simp only [Matrix.map_mul, Matrix.map_map] at this
    exact this
  rw [hF] at e1
  have e2 : G *ᵥ (fun a : Fin (B.R.N B.R.m) => p (TC.z0 X u a)) = fun a => p (TC.z0 X u a) := by
    funext i
    have := congrArg q (congrFun h2 i)
    exact (RingHom.map_mulVec q _ _ i).symm.trans this
  have hc0 : p ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := (map_ne_zero p).2 (piT_coe_ne_zero X u)
  have hz : (fun a : Fin (B.R.N B.R.m) => p (TC.z0 X u a)) =
      p ((X.piT u : 𝓞 B.host.E) : B.host.E) •
        (fun i : Fin (B.R.N B.R.m) => if (i : ℕ) = B.R.N B.R.m - 1 then (1 : ℂ) else 0) := by
    funext i
    simp only [TC.z0, Pi.smul_apply, smul_eq_mul]
    have := i.2
    by_cases h : (i : ℕ) + 1 = B.R.N B.R.m
    · rw [if_pos h, if_pos (by omega), mul_one]
    · rw [if_neg h, if_neg (by omega), mul_zero]
      exact map_zero p
  rw [hz, Matrix.mulVec_smul] at e2
  have e2' := smul_right_injective _ hc0 e2
  exact TC.BlockMatrixCriteria.isBlock_of_entries rfl rfl hN G G' _ _ (fun _ _ => rfl) (fun _ _ => rfl) e1 e2'

end GlobalTheory.EmbTopBlock
