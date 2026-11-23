import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EWtApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UfGLRatHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWHlatIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwLat

open GlobalTheory.Mem.Col2.RowTie

theorem natW_shW' {N : ℕ} (l : DomWeight N) (c : ℤ) : (GlobalTheory.Mem.Col2.shW l c).natW = l.natW := by
  funext i
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.2
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos hN, GlobalTheory.Mem.Col2.shW]
  congr 1
  ring

theorem delStd_shW' {K ι : Type} [Field K] [NumberField K] [Fintype ι] {N : ℕ} (lam : ι → DomWeight N) (c : ℤ) :
    delStd K (fun τ => GlobalTheory.Mem.Col2.shW (lam τ) c) = delStd K lam := by
  unfold delStd delSq
  simp only [natW_shW']

section Gen

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok)

theorem locW_lat_iff (hS : S.Ok) {G : ι → Matrix (Fin n) (Fin n) ℂ} {sh : ι → ℤ} (hsh : sh = shiftOf lam) {e : ι → E →+* ℂ}
    (he : e = embAt σ emb) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
    (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) (w : Pl.Pl)
    (Sp : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ))
    (hSp : ∀ Q, Q ∈ Sp ↔ ∃ z₀ ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delStd K lam), Q = MvPolynomial.map σ z₀)
    (lat : S.Cl → Submodule (𝓞 E) (Fin n → E)) (hlat : ∀ c, S.Lsh c.1 (S.rep c) = lat c) (x : (S.hlat emb lam h).V) :
    x ∈ locW Pl w (S.hlat emb lam h).L ↔ ∀ (c : S.Cl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (lat c : Set _) B →
      ∃ Q ∈ Sp, (show Frames G → ℂ from S.embF emb σ lam h x c) =
        fnOf G sh (Formalism.L2.Forms.atInf e (B⁻¹ : GL (Fin n) E).1) Q := by
  subst hsh he
  have hL : ∀ c, Submodule.IsLattice E (lat c) := fun c => hlat c ▸ hS.lsh_lat c.1 _
  have key : ∀ (c : S.Cl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (lat c : Set _) B →
      (x.1 c ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam (lat c)) ↔
      ∃ Q ∈ Sp, (show Frames G → ℂ from S.embF emb σ lam h x c) =
        fnOf G (shiftOf lam) (Formalism.L2.Forms.atInf (embAt σ emb) (B⁻¹ : GL (Fin n) E).1) Q) := by
    intro c B hB
    refine (BwLat.mem_localization_delAtr_fn emb σ lam (pw w) (hL c) (fun _ => B) (fun τ => BwLat.isBasisAt_of_isLocBasis
      (Pl.resChar_prime w) _ ((bc_mem_below _ _ _).2 (by rw [map_natCast]; exact Formalism.L2.Col.vl_resChar_mem Pl pw hval w)) hB)
      (x.1 c)).trans ⟨?_, ?_⟩
    · rintro ⟨z, hz, e⟩
      exact ⟨_, (hSp _).2 ⟨z, hz, rfl⟩, e⟩
    · rintro ⟨Q, hQ, e⟩
      obtain ⟨z, hz, rfl⟩ := (hSp Q).1 hQ
      exact ⟨z, hz, e⟩
  rw [GlobalTheory.Mem.Col2.mem_locW_hlat_iff emb Pl pw hval S lam h hS w x]
  simp only [hlat]
  unfold locW
  simp only [Formalism.L2.Col.vl_mem_span_intW_iff Pl pw hval w]
  refine ⟨fun H c B hB => (key c B hB).1 (H c), fun H c => ?_⟩
  haveI : Fact (Pl.resChar w).Prime := ⟨Pl.resChar_prime w⟩
  obtain ⟨B, hB⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (Pl.resChar w) E _ (hL c).fg (hL c).span_eq_top
  exact (key c B hB).2 (H c B hB)

end Gen

end GlobalTheory.Mem.Col2.TwLat

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.Mem.Col2.RowTie GlobalTheory.Mem.Col2.TwLat

set_option maxHeartbeats 1000000 in

theorem tw_lat_at : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ w, Formalism.L2.Forms.okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T w → ∀ x : (I.fm l u a).ptLat.V, x ∈ (I.fm l u a).SP w ↔ ∀ (c : (I.fm l u a).clsP) (Bm : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (I.rec7 l Z).host.E), IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (K.lat c : Set _) Bm → ∃ Pc ∈ IntSpan (I.rec7 l Z) w (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a ((I.fm l u a).ptEmb x) c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (I.rec7 l Z).host.E).1) Pc := by
  intro B X I hI hP l Z u a Q K hQ hQT hK w hw x
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hsg : (I.perIn u a).sgT = sgTG (D := I.rec7 l Z) (I.fm l u a) := by
    funext τ
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (k + 1) := by
      rw [hk, show B.R.m * (2 * k + 1 + 1) = 2 * (B.R.m * (k + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = k + 1 := by omega
    show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
      Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := congrArg shiftOf hsg.symm
  have hS : (I.stX a).Ok := (l.per u a).step
  exact locW_lat_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT (l.fmL u a).famP hS hsh hemb
    (I.rec7 l Z).what₂.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq w (IntSpan (I.rec7 l Z) w B.wts.sgW)
    (fun Q => by
      have h := GlobalTheory.LvT.Built.ValLat.mem_closure_iff B.embLL ((I.rec7 l Z).plEq w) (intW (I.rec7 l Z).what₂.places w)
        ((I.rec7 l Z).val_nonneg_iff w) B.wts.sgW Q
      rw [← delStd_shW' B.wts.sgW (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))] at h
      exact h)
    K.lat (fun c => (RowTie.Lsh_empty _).trans (hK.lat c).symm) x

end GlobalTheory.Mem.Col2.TC

end
