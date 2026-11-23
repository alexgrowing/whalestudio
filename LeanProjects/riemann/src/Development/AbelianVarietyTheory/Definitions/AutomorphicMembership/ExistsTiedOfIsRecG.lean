import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.LayerTwoModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G

theorem isRecG_retie {sc D Gt c H F} (h : IsRecG sc D Gt c H F) (g') : IsRecG sc D Gt c ⟨H.lev0, g'⟩ F := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  exact ⟨D0, Lc, I, ψ, hd, ⟨_, g'⟩, hL, _, B, hBs, hB, iK, lam, hK, hPos, CH, rfl⟩

theorem gatNum_of_isRecG {sc D Gt c H F} (h : IsRecG sc D Gt c H F) : GatNum sc D := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  intro u w hg
  exact ⟨rfl, rfl⟩

theorem exists_tied_of_isRecG {sc D Gt c H F} (h : IsRecG sc D Gt c H F) :
    ∃ g : GroupCompatibilityAll D Gt c, g.herm.lev0 = H.lev0 ∧ g.forms = F ∧ IsRecG sc D Gt c g.herm g.forms := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  exact ⟨groupCompatibilityOfRecursion D0 sc 1 Lc I ψ hd _ hL _ B hBs hB (CH.toHyp0 fun u w hg v s x =>
      pos_C D0 sc 1 Lc I ψ hd _ hL B hBs hB iK lam hK hPos u w hg v s x).toHyp fun u w h => isHyperbolicAt_rec_of_placeIdentification D0 u w h (I u w h),
    rfl, rfl, isRecG_retie ⟨D0, Lc, I, ψ, hd, _, hL, _, B, hBs, hB, iK, lam, hK, hPos, CH, rfl⟩ _⟩

section Stages
variable {B : Base} {C : Cols B} (W W' : RowsRest B C) (V : DivStage B C W) (V' : DivStage B C W') (S : SStage B C W)
  (S' : SStage B C W') (N : NStage B C W) (N' : NStage B C W') (G G' : GJStage B C)

theorem hP_assemble_eq (p) : hP (assemble B C W V S N G) p = hP (assemble B C W' V' S' N' G') p := rfl

theorem lamRec_stages (u g) : lamRec (assemble B C W V S N G) u g = lamRec (assemble B C W' V' S' N' G') u g := rfl

theorem tauRec_stages (w : B.places.Pl) [h : Fact (B.places.resChar w).Prime] (n) :
    @tauRec (assemble B C W V S N G) w h n = @tauRec (assemble B C W' V' S' N' G') w h n := rfl

theorem omTied_stages (δ : ℂ) :
    Formalism.L2.GlobalTheoryTheory.OmegaCompatible (assemble B C W V S N G) δ ↔ Formalism.L2.GlobalTheoryTheory.OmegaCompatible (assemble B C W' V' S' N' G) δ := Iff.rfl

end Stages

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem above_auto (w : ColW B f T) (v) : w.I.sel v ∈ aboveF (L := B.host.E) B.host.F v := by
  rw [aboveF, Set.Finite.mem_toFinset]
  exact HeightOneSpectrum.ext (w.ok.sel_ok v)

theorem vals_auto (w : ColW B f T) (a P) : ∃ z : B.LL, B.embLL z = (((w.I.xi a).val P : ℂˣ) : ℂ) :=
  ⟨_, (w.ok.xi_reads a _).symm⟩

theorem roots_auto (w : ColW B f T) (ht : TC.IsTw w.I) (a) (P) (hP : P ∈ w.I.Q a) :
    ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (𝓞 B.fields.E ⧸ P.asIdeal)) := by
  classical
  obtain ⟨z, hz⟩ := TC.root_of_ok w.ok ht.deep a ⟨P, Finset.mem_union_right _ hP⟩ (TC.Q_notMem_of_ok w.ok a P hP)
  have hq : (Formalism.L2.Col.qOf P : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  have hq0 : Formalism.L2.Col.qOf P ≠ 0 := Nat.cast_ne_zero.1 hq
  have h1 := Complex.isPrimitiveRoot_exp (Formalism.L2.Col.qOf P ^ (2 * B.R.m)) (pow_ne_zero _ hq0)
  rw [← hz] at h1
  have h2 : IsPrimitiveRoot z (Formalism.L2.Col.qOf P ^ (2 * B.R.m)) := h1.of_map_of_injective w.I.glob.σ₀.injective
  have hm : 2 * B.R.m = (2 * B.R.m - 1) + 1 := by have := B.R.two_le_m; omega
  have h3 := h2.pow (Nat.pos_of_ne_zero (pow_ne_zero _ hq0)) (a := Formalism.L2.Col.qOf P ^ (2 * B.R.m - 1)) (b := Formalism.L2.Col.qOf P)
    (by conv_lhs => rw [hm, pow_succ])
  exact ⟨_, h3⟩

theorem exists_over (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 L), (p : 𝓞 L) ∈ v.asIdeal := by
  have hu : ¬ IsUnit (p : 𝓞 L) := fun h => by
    have h1 := h.map (Algebra.norm ℤ)
    rw [show (p : 𝓞 L) = algebraMap ℤ (𝓞 L) p by simp, Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne',
      Int.isUnit_iff_natAbs_eq] at h1
    exact hp.one_lt.ne' (by simpa using h1)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(p : 𝓞 L)}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hp' : (p : 𝓞 L) ∈ M := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨M, hM.isPrime, fun h => hp.ne_zero (by rw [h] at hp'; exact_mod_cast (Ideal.mem_bot.1 hp'))⟩, hp'⟩

theorem under_mem (w : ColW B f T) {p : ℕ} {v : HeightOneSpectrum (𝓞 B.host.F)} (hv : (p : 𝓞 B.host.F) ∈ v.asIdeal) :
    (p : 𝓞 B.host.K) ∈ ((show HeightOneSpectrum (𝓞 B.host.E) from w.I.sel v).under (𝓞 B.host.K)).asIdeal := by
  have h := w.ok.sel_ok v
  rw [← h] at hv
  have h1 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (p : 𝓞 B.host.F) ∈ (w.I.sel v).asIdeal := hv
  show algebraMap (𝓞 B.host.K) (𝓞 B.host.E) (p : 𝓞 B.host.K) ∈ (w.I.sel v).asIdeal
  rw [map_natCast] at h1 ⊢
  exact h1

theorem pinned_iff (w : ColW B f T) : Pinned K B f T w ↔ TC.IsTw w.I ∧ ColIn.JetsIn w.I ∧ Half B w.I.sel := by
  refine ⟨fun ⟨p⟩ => ⟨p.isTw, p.jets, p.half⟩, fun ⟨a, b, c⟩ => ?_⟩
  obtain ⟨v₀, h₀⟩ := exists_over B.host.F B.host.pde_prime
  obtain ⟨v₁, h₁⟩ := exists_over B.host.F B.host.pde'_prime
  exact ⟨⟨a, b, (base_fields_primes_ok B w.px).1, above_auto w, c,
    ⟨_, _, under_mem w h₀, under_mem w h₁, fun v _ => w.I.sel v, fun v _ => w.I.sel v,
      fun v hv => ⟨above_auto w v, c v v₀ _ B.host.pde_prime hv h₀⟩,
      fun v hv => ⟨above_auto w v, c v v₁ _ B.host.pde'_prime hv h₁⟩⟩,
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩, fun a P _ => vals_auto w a P, roots_auto w a⟩⟩

theorem gIs2_iff (w : ColW B f T) (G : GJStage B w.C) : GIs2 K w G ↔
    ∀ W V S N, Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColumnDataSplitPrimes K w ⟨W, V, S, N, G⟩) :=
  ⟨fun h W V S N => ⟨(h W V S N).1, (h W V S N).2.2⟩,
    fun h W V S N => let ⟨a, ⟨t⟩⟩ := h W V S N; ⟨a, gatNum_of_isRecG t.isRec, ⟨t⟩⟩⟩

theorem cond_eq_of_twisted {w : ColW B f T} {Z : w.Lt} {Wt} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (v)
    (hv : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0) : nch.Q v = T.Q v := by
  have h1 := (n.tp.psi_is v hv).ram
  rw [n.psi] at h1
  ext P
  have := (h1 P).symm.trans ((T.psi_is v).ram P)
  exact not_iff_not.1 this

end GlobalTheory.Mem.Top.Bl.LayerTwoModel

end
