import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.TiedValBwG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem mem_locW_hlat_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok), S.Ok → ∀ (w : Pl.Pl) (x : (S.hlat emb lam h).V), x ∈ locW Pl w (S.hlat emb lam h).L ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  intro E K ι _ _ _ _ _ _ _ emb Pl pw hv n S lam h hS w x
  unfold locW
  simp only [vl_mem_span_intW_iff Pl pw hv]
  unfold Formalism.HermitianLatticesTheory.localization₂
  constructor
  · rintro ⟨s, hs, hsx⟩ c
    exact ⟨s, hs, hsx c⟩
  · classical
    intro hx
    choose t ht htx using hx
    have : ∀ b, Finite (MulAction.orbitRel.Quotient (S.G b) (S.D b)) := hS.fin_orb
    let _ : Fintype S.Cl := Fintype.ofFinite _
    refine ⟨∏ c, t c, Submonoid.prod_mem _ fun c _ => ht c, fun c => ?_⟩
    have hc := (delAtr emb lam (S.Lsh c.1 (S.rep c))).smul_mem (∏ d ∈ Finset.univ.erase c, t d) (htx c)
    rw [← mul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ c)] at hc
    exact hc

end GlobalTheory.Mem.Col2
