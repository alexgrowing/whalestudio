import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalBasisRepLatticeIntegralCoordsSpecStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWDelAtrIffStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanMapNabKDelK

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem bc_invTrK_embGL {B : Base} {n : ℕ} (g : GL (Fin n) B.fields.E) :
  (fun τ => Formalism.UG.bc B.embLL (invTrK (embGL B.fields.emb g) τ)) = invTrK (embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) g) := by
  funext τ
  apply Units.ext
  ext i j
  simp [invTrK, inside₂, embGL, Formalism.UG.bc, Formalism.L2.Col.embAt]
  rw [← Matrix.map_map, ← Formalism.L2.Col.map_inv_matrix, ← Formalism.L2.Col.map_inv_matrix, ← Formalism.L2.Col.map_inv_matrix]
  rfl

theorem intSpan_smul (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam) : D.what₂.embLL r • p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan at *
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    exact ⟨r * r', f, mul_mem hr hr', hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem latCo_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl)
    (y : (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).V) (hy : y ∈ (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).L) :
    GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y ((I.perIn u a).tilC c)) ∈
      Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) := by
  set v' := ((I.chIn u a).S B.R.m).rho B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (I.perIn u a).b0 (((I.chIn u a).S B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))
          (y.1 (((I.chIn u a).S B.R.m).cl (I.perIn u a).b0 ((I.perIn u a).tilPt c))) with hv'
  have hmem := GlobalTheory.LvT.BuiltChain.rho_mv_mem B.fields.emb ((I.chIn u a).S B.R.m) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y hy (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  have e1 : GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y ((I.perIn u a).tilC c)) =
      actP (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (invTrK (embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bM I u a w c)⁻¹))
        (MvPolynomial.map B.embLL v'.1) := by
    unfold GlobalTheory.PerQ.Co.coM
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    congr 1
    rw [← GlobalTheory.LvT.BuiltChain.polOf_evV B.fields.emb B.embLL]
    congr 1
    rw [hv', GlobalTheory.LvT.BuiltChain.evV_rho]
    rfl
  rw [e1, ← bc_invTrK_embGL, ← GlobalTheory.ValCmp.use₂]
  have hB := (GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c).2.2.2
  have hM : Submodule.IsLattice B.fields.E (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c)) :=
    ((l.ch u a).step B.R.m).lsh_lat (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  have hnat : ∀ τ, ((GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) τ).natW = (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ).natW := by
    intro τ
    show (GlobalTheory.Mem.Col2.shW (Examples₂.lamOf (B.hcW u τ) B.R.m) _).natW = (Examples₂.lamOf (B.hcW u τ) B.R.m).natW
    funext i
    have hN : 0 < B.R.N B.R.m := lt_of_le_of_lt (Nat.zero_le _) i.2
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hN, GlobalTheory.Mem.Col2.shW]
    congr 1
    ring
  exact (GlobalTheory.T.mem_locW_delAtr_iff' B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq
    (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) hnat _ hM w _ hB v').1 (Submodule.subset_span hmem)

theorem latCo_gen {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) :
    ∀ x ∈ Submodule.span (intW B.places w) ((((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).L : Set (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).V),
      GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) x ((I.perIn u a).tilC c)) ∈
        Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact latCo_one I hI l Z u a w c y hy
  | zero => rw [map_zero, Pi.zero_apply, map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, Pi.add_apply, map_add]; exact add_mem hy hz
  | smul r y _ hy =>
    have e : r • y = (r : B.LL) • y := rfl
    rw [e, LinearMap.map_smulₛₗ, Pi.smul_apply, map_smul]
    exact intSpan_smul (I.rec7 l Z) w _ (r : B.LL) r.2 _ hy

theorem latCo_mem_intSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ x ∈ ((I.tw l l0 Z).fm u a).S (I.rec7 l Z).R.m w, ∀ c, GlobalTheory.PerQ.Co.coM I u a w c (((I.tw l l0 Z).fm u a).emb (I.rec7 l Z).R.m x (((I.tw l l0 Z).fm u a).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) :=
  fun I hI l Z _ u a w x hx c => latCo_gen I hI l Z u a w c x hx

end GlobalTheory.PerQ.Co

end
