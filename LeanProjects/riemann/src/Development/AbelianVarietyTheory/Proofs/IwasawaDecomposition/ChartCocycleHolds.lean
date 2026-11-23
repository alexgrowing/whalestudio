import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsTransitionUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.Models (LevComp)

namespace GlobalTheory.LocM.Cocycle

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem levComp_comp {l₁ l₂ l₃ : Level H} {B₁ B₂ B₃ : Type} [CommRing B₁] [CommRing B₂] [CommRing B₃]
    {b₁ : Base l₁ B₁} {b₂ : Base l₂ B₂} {b₃ : Base l₃ B₃} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp B₁}
    {s₂ : S₂ ⟶ Sp B₂} {s₃ : S₃ ⟶ Sp B₃} (o₁ : Obj Dw l₁ b₁ s₁) (o₂ : Obj Dw l₂ b₂ s₂) (o₃ : Obj Dw l₃ b₃ s₃)
    (h₁ : l₁.Dvd l₂) (h₂ : l₂.Dvd l₃) {r : S₂ ⟶ S₁} {r' : S₃ ⟶ S₂} (ν : SABMap o₂.t o₁.t r)
    (ν' : SABMap o₃.t o₂.t r') (hν : LevComp o₂ o₁ r ν) (hν' : LevComp o₃ o₂ r' ν') :
    ∃ n : SABMap o₃.t o₁.t (r' ≫ r), n.φ = ν'.φ ≫ ν.φ ∧ LevComp o₃ o₁ (r' ≫ r) n := by
  obtain ⟨n, hn⟩ := LevelCover.sab_comp ν' ν rfl
  have hM₂ : 0 < l₂.M := by have := l₂.three_le; omega
  have eM : l₃.M / l₁.M = l₃.M / l₂.M * (l₂.M / l₁.M) := by
    rw [Nat.div_mul_div_comm h₂.1 h₁.1, mul_comm l₃.M, Nat.mul_div_mul_left _ _ hM₂]
  have eA : l₃.A / l₁.A = l₃.A / l₂.A * (l₂.A / l₁.A) := by
    rw [Nat.div_mul_div_comm h₂.2.2 h₁.2.2, mul_comm l₃.A, Nat.mul_div_mul_left _ _ l₂.A_pos]
  refine ⟨n, hn, fun a => ?_, fun a => ?_⟩
  · rw [eM, pow_mul, hn, ← Category.assoc, LevelCover.sec_pow ν' _ _ (hν'.1 a), Category.assoc, hν.1 a,
      Category.assoc]
  · rw [eA, pow_mul, hn, ← Category.assoc, LevelCover.sec_pow ν' _ _ (hν'.2 a), Category.assoc, hν.2 a,
      Category.assoc]

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}

theorem exists_sab_of_isTrans {i i₂ : Idx H p} {τ : (Y i₂).X ⟶ (Y i).X} {mu : SABMap (Y i₂).t (Y i).t τ}
    (h : IsTrans i i₂ τ mu) :
    ∃ (b : i.c.V W →+* i₂.c.V W) (r : (Xo i₂.l).XF i₂.c ⟶ (Xo i.l).XF i.c) (ν : SABMap (Y i₂).oF.t (Y i).oF.t r),
      IsIncl b ∧ (Y i₂).j ≫ τ = r ≫ (Y i).j ∧ τ ≫ (Y i).s = (Y i₂).s ≫ spMap b ∧
      ν.φ ≫ (Y i).m.φ = (Y i₂).m.φ ≫ mu.φ ∧ LevComp (Y i₂).oF (Y i).oF r ν := by
  obtain ⟨b, π', r, hb, h₁, h₂, -, h₃, h₄, h₅⟩ := h
  have e : τ ≫ (Y i).s = (Y i₂).s ≫ spMap b := by
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨n, hn⟩ := LevelCover.sab_comp (Y i₂).m mu h₃
  obtain ⟨ν, hν⟩ := LevelCover.sab_cancel (Y i).m n r rfl
  refine ⟨b, r, ν, hb, h₃, e, hν.trans hn, fun a => ?_, fun a => ?_⟩
  · exact LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₄ a)
  · exact LevelCover.sec_cancel ν (Y i).m _ _ (by rw [hν, hn]; exact h₅ a)

theorem cocycle : CocycleSt := by
  intro E _ _ _ H Dw Xo p W Y i₁ i₂ i₃ τ mu τ' mu' τ'' mu'' h₁₂ h₂₃ h h' h''
  obtain ⟨b, r, ν, hb, hj, hs, hν, hl⟩ := exists_sab_of_isTrans h
  obtain ⟨b', r', ν', hb', hj', hs', hν', hl'⟩ := exists_sab_of_isTrans h'
  obtain ⟨b'', r'', ν'', hb'', hj'', hs'', hν'', hl''⟩ := exists_sab_of_isTrans h''
  obtain ⟨n, hn, hln⟩ := levComp_comp _ _ _ h₁₂ h₂₃ ν ν' hl hl'
  have hbb : spMap b' ≫ spMap b = spMap b'' := by
    have e : b'.comp b = b'' :=
      RingHom.ext fun x => Subtype.ext (Subtype.ext (((hb' (b x)).trans (hb x)).trans (hb'' x).symm))
    rw [ModelRelProbe.spMap_comp, e]
  have hr : (r' ≫ r) ≫ pullback.snd _ _ = r'' ≫ pullback.snd _ _ := by
    have := mono_spMap_subtype (i₁.c.V W)
    rw [← cancel_mono (spMap (i₁.c.V W).subtype), Category.assoc, Category.assoc, Category.assoc,
      ← ModelRelProbe.j_over (Y i₁), ← reassoc_of% hj, ← reassoc_of% hj', ← reassoc_of% hj'', hs, hs'',
      reassoc_of% hs', hbb]
  have hS := TransitionUnique.isReduced_XF (Xo i₃.l) i₃.c
  have hrr : r' ≫ r = r'' := TransitionUnique.map_unique (Y i₁) n ν'' hr
    (fun a => ⟨_, hln.1 a, hl''.1 a⟩) (fun a => ⟨_, hln.2 a, hl''.2 a⟩)
  subst hrr
  have hd : i₁.l.Dvd i₃.l := ⟨dvd_trans h₁₂.1 h₂₃.1, h₂₃.2.1.trans h₁₂.2.1, dvd_trans h₁₂.2.2 h₂₃.2.2⟩
  have hφ : n.φ = ν''.φ :=
    obj_rigid_closed abelianSchemeLaws_all.1 E H Dw i₁.l _ _ (baseKA i₁.l) (baseOfFinerLevel hd.2.2) _ _ _ _
      (Y i₁).oF (ObjLower.lower (Y i₃).oF hd (baseOfFinerLevel_rho hd.2.2) (baseOfFinerLevel_zeta hd.2.2))
      (r' ≫ r) (Or.inl hS) n ν'' fun a => ⟨_, hln.1 a, hl''.1 a⟩
  rw [← hν'', ← hφ, hn, Category.assoc, hν, ← Category.assoc ν'.φ, hν', Category.assoc]

end GlobalTheory.LocM.Cocycle
