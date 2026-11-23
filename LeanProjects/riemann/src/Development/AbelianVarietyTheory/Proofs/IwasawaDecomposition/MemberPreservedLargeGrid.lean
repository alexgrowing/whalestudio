import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlot
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {N : NExt hL} {S : SExt} {Γ : GeoP} {A : AtP}

def builtA_drop {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (prmR (NEa hL N A) S Γ).s K w Z c) : Built (prmR N S Γ).s K w Z c :=
  { b with nx := ⟨b.nx.1, b.nx.2.1⟩ }

def builtA_add {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T}
    (b : Built (prmR N S Γ).s K w Z c) (a : A K B f T) : Built (prmR (NEa hL N A) S Γ).s K w Z c :=
  { b with nx := ⟨b.nx.1, b.nx.2, PLift.up a⟩ }

theorem isBuiltE_prmA_iff (K X f T c) :
    IsBuiltE (prmR (NEa hL N A) S Γ).s K X f T c ↔ IsBuiltE (prmR N S Γ).s K X f T c ∧ A K X.B f T := by
  constructor
  · rintro ⟨w, Z, c', ⟨b, hb⟩, he⟩
    exact ⟨⟨w, Z, c', ⟨builtA_drop b, hb⟩, he⟩, b.nx.2.2.down⟩
  · rintro ⟨⟨w, Z, c', ⟨b, hb⟩, he⟩, a⟩
    exact ⟨w, Z, c', ⟨builtA_add b a, hb⟩, he⟩

theorem isGoodE_prmA_iff (K X f T c) :
    IsGoodE (prmR (NEa hL N A) S Γ).s K X f T c ↔ IsGoodE (prmR N S Γ).s K X f T c ∧ A K X.B f T := by
  constructor
  · rintro ⟨w, Z, c', ⟨⟨b, hb⟩, g⟩, he⟩
    exact ⟨⟨w, Z, c', ⟨⟨builtA_drop b, hb⟩, g⟩, he⟩, b.nx.2.2.down⟩
  · rintro ⟨⟨w, Z, c', ⟨⟨b, hb⟩, g⟩, he⟩, a⟩
    exact ⟨w, Z, c', ⟨⟨builtA_add b a, hb⟩, g⟩, he⟩

theorem memberE_prmR_NEa : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP) (A : AtP), EvLgG A →
    MemberE (prmR N S Γ).s → MemberE (prmR (NEa hL N A) S Γ).s := by
  intro hL N S Γ A hA ⟨hB, h1, hE, h2⟩
  refine ⟨hB, ?_, ?_, ?_⟩
  · have h := Step.and (KP := KPx) h1 (Step.of_evLgG (p := fun _ B _ T => T = TwDat.untw B T.pl) hA)
    refine EvG.imp h fun K _ _ _ _ H => H.imp fun B f T _ G k u v => ?_
    obtain ⟨⟨C, W, V, S, N, Gs, c, q⟩, a⟩ := G k u v
    exact ⟨C, W, V, S, N, Gs, c, (isBuiltE_prmA_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).2 ⟨q, a⟩⟩
  · exact EvG.imp hE fun K _ _ _ _ H => H.imp fun B f T _ G k u C W V S N Gs c q =>
      G k u C W V S N Gs c ((isBuiltE_prmA_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).1 q).1
  · have hR : LargeBaseConditionG KPx (IsBuiltE (prmR N S Γ).s) (fun K X f T _ => A K X.B f T) :=
      EvG.imp hA fun K _ _ _ _ H => H.imp fun B f T _ a _ C W V S N Gs c _ => a
    have h2' := SecondG.sAnd_of_largeBase KPx _ _ _ hB hR h2
    refine EvG.imp h2' fun K _ _ _ _ H => H.imp fun B f T _ G k u C W V S N Gs c q e Av S₂ hS₂ => ?_
    obtain ⟨B', f', T', a1, a2, a3, a4, a5, C', W', V', S', N', G', c', q', tw, g', a⟩ :=
      G k u C W V S N Gs c ((isBuiltE_prmA_iff K ⟨B, C, W, V, S, N, Gs⟩ f T c).1 q).1 e Av S₂ hS₂
    exact ⟨B', f', T', a1, a2, a3, a4, a5, C', W', V', S', N', G', c',
      (isBuiltE_prmA_iff K ⟨B', C', W', V', S', N', G'⟩ f' T' c').2 ⟨q', a⟩, tw,
      (isGoodE_prmA_iff K ⟨B', C', W', V', S', N', G'⟩ f' T' c').2 ⟨g', a⟩⟩

end GlobalTheory.Mem.LiteralAutomorphy
