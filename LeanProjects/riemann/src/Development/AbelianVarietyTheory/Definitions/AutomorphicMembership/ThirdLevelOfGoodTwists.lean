import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

noncomputable section

namespace GlobalTheory.HeightCounting.Up.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem kept_refl {D : D7} (c : NChoice D) : Kept c c :=
  ⟨by constructor <;> rfl, by constructor <;> rfl, by constructor <;> rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem kept_withLoc {D : D7} (L : LocAll (lay0 D)) (c : NChoice D) : Kept c (chL L c) :=
  ⟨by constructor <;> rfl, by constructor <;> rfl, by constructor <;> rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

def levelThreeIndependentOfChoices {N : NExt hL} {S S' : SExt} {Γ Γ' : GeoP} {Z : w.Lt} (v : Lv3 (prmR N S Γ).s K w Z) : Lv3 (prmR N S' Γ').s K w Z :=
  { g := v.g, coh := v.coh, Wt := v.Wt, p0 := v.p0, what₂ := v.what₂, rx := v.rx, nch := v.nch, n := v.n, xd := v.xd, chiT := v.chiT,
    nx := v.nx }

theorem third_level_of_good_twists {S : SExt} {Γ : GeoP} (h : Has3 (prmR (NEg hL) S Γ).s K B f T w) : Has3 (prmR (NEb hL) S Γ).s K B f T w :=
  let ⟨Z, ⟨v⟩⟩ := h
  ⟨Z, ⟨⟨⟨v.g, v.coh, v.Wt, v.p0, v.what₂, v.rx⟩, v.nch, v.n, v.xd, v.chiT, ⟨v.nx.1, v.nx.2.1⟩⟩⟩⟩

theorem qOf_off (v : B.places.Pl) (h : v ∉ P.Wt) : QOf P v = ∅ := if_neg h

theorem qOf_on (v : B.places.Pl) (h : v ∈ P.Wt) : QOf P v = T.Q v := if_pos h

theorem qOf_eq (v : B.places.Pl) : QOf P v = T.Q v := by
  by_cases h : v ∈ P.Wt
  · exact qOf_on v h
  · rw [qOf_off v h]
    refine (Finset.eq_empty_of_forall_notMem fun u hu => ?_).symm
    have h1 := ((T.psi_is v).ram u).1 (by rw [P.supp v h]; exact fun _ _ => rfl)
    exact h1 hu

theorem mem_of_twisted (x : St P) (v : B.places.Pl) (h : TwistedAt (Dof x) v) : v ∈ P.Wt := by
  by_contra hv
  exact h (P.q.mu.off v hv)

theorem del_mul_ne_one {p : ℕ} (hp : p.Prime) (hS : p ∈ offSet B.toPre) {δ : HChar B.host.E} (hδ : IsDelta (H := B.host) p δ)
    (v : B.places.Pl) : δ * T.psi v ≠ 1 := by
  intro h
  obtain ⟨Q, hQ, hpQ⟩ : ∃ Q : Ideal (𝓞 B.host.E), Q.IsMaximal ∧ ((p : ℕ) : 𝓞 B.host.E) ∈ Q := by
    have hne : Ideal.span {((p : ℕ) : 𝓞 B.host.E)} ≠ ⊤ := by
      intro ht
      have := congrArg Ideal.absNorm ht
      rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at this
      have h2 : Algebra.norm ℤ ((p : ℕ) : 𝓞 B.host.E) = (p : ℤ) ^ Module.finrank ℤ (𝓞 B.host.E) := by
        rw [← map_natCast (algebraMap ℤ (𝓞 B.host.E)), Algebra.norm_algebraMap]
      rw [h2, Int.natAbs_pow, Int.natAbs_natCast] at this
      rcases Nat.pow_eq_one.1 this with h3 | h3
      · exact hp.one_lt.ne' h3
      · exact Module.finrank_pos.ne' h3
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    exact ⟨Q, hQ, hle (Ideal.subset_span rfl)⟩
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hpQ))
  let u : HeightOneSpectrum (𝓞 B.host.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hu : OverP B.host p u := hpQ
  have hψ : (T.psi v).UnrAt u := by
    by_contra hn
    obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 u hn
    have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 B.host.E) ∈ u.asIdeal := Ideal.absNorm_mem _
    by_cases e : Ideal.absNorm u.asIdeal = p
    · exact h2 (e ▸ hS)
    · obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 B.host.E) (p : 𝓞 B.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes h1 hp).2 e)
      exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ hpQ)))
  have h15 := (hδ.ine u hu 1).1 fun x hx => by
    have e := congrArg (fun χ : HChar B.host.E => χ.loc u x) h
    simp only [HChar.loc_mul, hψ x hx, mul_one] at e
    rw [pow_one, e]
    rfl
  omega

theorem twisted_iff (x : St P) (v : B.places.Pl) : TwistedAt (Dof x) v ↔ v ∈ P.Wt := by
  refine ⟨mem_of_twisted x v, fun hv h => ?_⟩
  have h1 : P.q.W₀.muTw v = w.C.mu0 := (P.q.mu.on v hv).symm.trans h
  have h2 := P.q.mu.tw v
  rw [h1] at h2
  have h3 : T.xiTw f v = 1 := h2.symm.trans w.ok.trueColumnChoices_heckeChar_reference_eq_one
  unfold TwDat.xiTw at h3
  split_ifs at h3
  · exact del_mul_ne_one B.host.pde'_prime (by simp [offSet]) f.isDel' v h3
  · exact del_mul_ne_one B.host.pde_prime (by simp [offSet]) f.isDel v h3

theorem eta_zero {x : St P} (l : LA hL x) (j : ℕ) (v : B.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ B.R.m) : x.o.η j v = 0 := by
  have h := x.o.N.etaJ_tie j v h1 h2
  have hE : IsEmpty x.o.N.nd.Loc := l.a.A.bare
  rw [Finset.eq_empty_of_isEmpty (x.o.N.nd.locs j v), Finset.sum_empty] at h
  exact h

theorem chain (h0 : StepW Start HasBare) (hA : SA hL) (hM : SMt) (hR : SRat hL) (hC : SCusp hL) (b0 : SettingsFormsExist hL) (b1 : SeriesExist hL)
    (b2 : SB2 hL) (hc : SC hL) (hF : SFin hL) (S : SExt) (Γ : GeoP) : StepW Start (Has3 (prmR (NEb hL) S Γ).s) := by
  refine (h0.and (StepW.and hA (StepW.and hM (StepW.and hR (StepW.and hC (StepW.and b0 (StepW.and b1 (StepW.and b2
    (StepW.and hc hF))))))))).trans (StepW.of_all ?_)
  rintro K B f T w - - ⟨⟨P, x, hx, -⟩, hA, hM, hR, hC, b0, b1, b2, hc, hF⟩
  obtain ⟨x1, ⟨a⟩, -⟩ := hA P x hx
  obtain ⟨m⟩ := hM P x1
  obtain ⟨r⟩ := hR P x1 a
  obtain ⟨x2, ⟨l0⟩⟩ := b0 P x1 { toLA := a, mt := m, rat := r, cusp := hC P x1 a }
  obtain ⟨x3, ⟨l1⟩⟩ := b1 P x2 l0
  obtain ⟨x4, ⟨l2⟩⟩ := b2 P x3 l1
  obtain ⟨c⟩ := hc P x4 l2
  obtain ⟨Z, v, -⟩ := hF P x4 { toStrictHenselianAcyclic := l2, c := c } S Γ
  exact ⟨Z, ⟨v⟩⟩

end GlobalTheory.HeightCounting.Up.Model

end
