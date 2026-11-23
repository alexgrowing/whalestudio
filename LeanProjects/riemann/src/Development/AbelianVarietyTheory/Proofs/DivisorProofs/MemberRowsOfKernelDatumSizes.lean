import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
import Formalism.LocalToGlobal.Divisibility.NumbersLink
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnsMemberRowsOfLogLevelLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfNumReads
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem rowsBody_of_kerTies : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) [IsTotallyComplex t.X.K] (W : Formalism.L2.Col.Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (hX : t.X.Ok) (Bs : DefBase t.X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 t.X.E t.Pr.vGs D.R.r → t.X.K)) (tup : Bs.Tup → D.what₂.Tup) (hP : ∀ τ, (mtildeGSD W t.Ch t.sel (t.tup (tup τ)) (rPsymF (R := D.R) t.Ch)).Ok) (b : ∀ τ, D.what₂.Word → (t.idx (tup τ)).β (t.m2 + 1)) (hY : ∀ τ x, YbHyp (R := D.R) t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) (t.word x) t.m2 (b τ x)) (hK : ∀ τ x, KerEquivC W t.Ch t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) t.amb (t.word x) t.m2 (b τ x) (hY τ x) (rPsymF (R := D.R) t.Ch)) (hF : ∀ τ x j, (chF W t.sel (t.tup (tup τ)) (t.idx (tup τ)) (t.word x) j).Ok) (hE : ∀ x, (evGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch) (t.word x)).Ok) (ev : ∀ τ, (Fin (Df.nV τ) → t.X.K) →ₗ[t.X.K] V0X W t.Ch t.sel (t.tup (tup τ)) Xg (rPsymF (R := D.R) t.Ch)) (u : D.what₂.Word) (eJ : Bs.J ≃ Fin D.R.m) (Nc lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) Nc lam0 c0 ce Ch Sw C1), tup Bs.μ0 = D.what₂.mu0 → KerTies t W Del h0 → KerSizes t W Del h0 CY CT → C0 ≤ Ch → (∀ v : InfinitePlace t.X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun t.X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) (fun τ => t.idx_ok (tup τ)) hP D.what₂.Word t.word b hY (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK) hF ev) u (memQ (A := (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK)) (hF := hF) hE (x := u)) (colsIn W t.Ch hX t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.idx (tup Bs.μ0)) (t.idx_ok (tup Bs.μ0)) (t.word u)) (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) ∧ ∀ v, IsUnit ((MramH W t.Ch hX (t.word u)).X v).det := by
  intro CY CT hCT
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.columnsMemberRows_of_logLevel_le CY CT hCT
  refine ⟨C0, fun D L hT Gi Gl K Y cX ex t _ W Del h0 hX Bs Df Xg tup hP b hY hK hF hE ev u eJ Nc lam0 c0 ce Ch Sw C1 H hmu hTi hS hC hPD hFr => ?_⟩
  obtain ⟨pl, hpl⟩ := hTi.wts
  have hmu0 : t.tup (tup Bs.μ0) = 1 := hmu ▸ hTi.mu0
  have hsh : (t.cst (tup Bs.μ0)).sharp = true := by rw [hmu]; exact hTi.sharp
  have hfld : FieldOfDefinition W t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.word u) t.amb := by
    rw [hmu]; exact hTi.fld u
  have hlog : Real.log (t.Pr.T (t.word u) : ℝ) ≤ CT * D.R.m * L.sc.L := by rw [t.T_rec u]; exact hS.logT u
  have hRd : Reads (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (t.Pr.T (t.word u))
      (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) := by
    rw [t.T_rec u]; exact NumReads.ofNum_reads _ _ eJ _ _ Nc lam0 c0 ce Ch Sw C1 H
  have hm2 := hTi.m2
  have hcc := t.cc_rec
  have hsz := hS.sizes
  have hrw := hS.what₂ u
  have hho := hTi.host
  have hch := hTi.chr
  have han := hTi.an
  have hwt := hpl u
  clear hTi hS hpl
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, X, seam, seam_ok, Pr, pr_ok, g_rec, ChT, sel, S, word, T_rec, tupT, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  dsimp only at *
  subst hm2
  subst hcc
  exact hC0 D (ofRecord D L Del h0) X seam Pr W ChT glob sel S hX Bs Df Xg (fun τ => tupT (tup τ)) (fun τ => cst (tup τ))
    (fun τ => idx (tup τ)) (fun τ => idx_ok (tup τ)) hP D.what₂.Word word b hY δ B χ cD hK hF hE ev pl u (letterOf D L Del h0 u) eJ _
    hho hwt hch han hmu0 hsh hfld hsz hrw hlog hRd hC hPD hFr

end GlobalTheory.ColRows
