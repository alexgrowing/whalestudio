import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def FineUniqP : Prop :=
  ∀ (Δ : Segment k) {N : ℕ} (hd : ∑ a, (Zc.Seg.dec Δ a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ → τ.IsIrreducible →
    ∀ f : τ.IntertwiningMap (prodIrr (Zc.Seg.dec Δ) hd), Function.Injective f → IsLSeg Δ τ

theorem exists_emb_of_cast {h h' N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (e : h = h') (x : Fin h → IrrGL k) (y : Fin h' → IrrGL k)
    (hxy : ∀ i, x i = y (Fin.cast e i)) (hd : ∑ a, (x a).1 = N) (f : τ.IntertwiningMap (prodIrr x hd))
    (hf : Function.Injective f) :
    ∃ hd' : ∑ a, (y a).1 = N, ∃ g : τ.IntertwiningMap (prodIrr y hd'), Function.Injective g := by
  subst e
  obtain rfl : x = y := funext fun i => by simpa using hxy i
  exact ⟨hd, f, hf⟩

theorem decW_get_eq (Γ : Segment k) (e : (decW Γ).length = Γ.len) (i : Fin (decW Γ).length) :
    (decW Γ).get i = Zc.Seg.dec Γ (Fin.cast e i) := by
  exact List.get_ofFn (fun a : Fin Γ.len => Γ.term (Fin.rev a)) i

theorem decLP (hF : FineUniqP k) : DecLP k := by
  intro Γ σ h
  obtain ⟨hd, f, hf⟩ := h
  have e : (decW Γ).length = Γ.len := List.length_ofFn
  obtain ⟨hd', g, hg⟩ := exists_emb_of_cast σ.rep e (decW Γ).get (Zc.Seg.dec Γ) (decW_get_eq Γ e) hd f hf
  exact hF Γ hd' σ.rep σ.2.rep.smooth σ.2.rep.irr g hg

end PositivityTheory.Exh

end
