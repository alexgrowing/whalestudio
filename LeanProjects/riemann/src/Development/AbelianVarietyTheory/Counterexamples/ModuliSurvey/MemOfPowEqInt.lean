import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ArcInTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem mem_of_pow_eq_int {F : Type} [Field F] (V : ValuationSubring F) (x : F) (n : ℕ) (hn : 0 < n) (m : ℤ)
    (h : x ^ n = m) : x ∈ V := by
  have hi : IsIntegral V x := by
    refine IsIntegral.of_pow hn ?_
    rw [h]
    simpa using isIntegral_algebraMap (R := V) (A := F) (x := (m : V))
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 hi
  exact hy ▸ y.2

theorem exists_values (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  refine ⟨⟨⟨_, GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c⟩, mem_of_pow_eq_int _ _ 2 two_pos (-(H.d : ℤ)) ?_⟩,
    ⟨⟨_, GlobalTheory.HostModel.zeta_A_mem_coeff c⟩, mem_of_pow_eq_int _ _ l.A l.A_pos 1 ?_⟩, rfl, rfl⟩
  · apply Subtype.ext
    simpa using H.sqrt_neg_disc_sq
  · apply Subtype.ext
    simpa [zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one

theorem int_ne_rt (c : Coeff l) (r : ℤ) : ((Int.castRingHom c.F r : c.F) : ℂ) ≠ H.rt0 := by
  intro h
  have h1 : ((r : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [← H.sqrt_neg_disc_sq, ← h]; simp
  have h2 : r ^ 2 = -(H.d : ℤ) := by exact_mod_cast h1
  have h3 := H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem nonempty_int (D : Datum H) (c : Coeff l) :
    Nonempty (ArcIn D l (Int.castRingHom c.F) c.F (Int.castRingHom c.F)) :=
  let a := GlobalTheory.HostModel.arcIn c c.F (RingHom.id _)
  ⟨{ D₀ := a.D₀, mod := a.mod, oa := a.oa, nontriv := a.nontriv, even := a.even, bimult := a.bimult, gen := a.gen
     w0 := a.w0, be := a.be, be_symm := a.be_symm, be_pos := a.be_pos, be_adj := a.be_adj, be_dvd := a.be_dvd
     eta := fun _ => a.eta 0, etaA := fun _ => a.etaA 0
     geom := fun _ _ _ _ r _ hr => absurd hr (int_ne_rt c r) }⟩

open Classical in

def changeOff {D : Datum H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) (e : D.La → QkPt a.D₀ (FractionRing O') l.M) :
    ArcIn D l β O' b :=
  { a with
    eta := fun v => if v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) then a.eta v else e v
    geom := fun F _ _ _ r z hr hz f hf => by
      obtain ⟨h₁, I, h₂, h₃, h₄⟩ := a.geom F r z hr hz f hf
      refine ⟨h₁, I, h₂, h₃, fun v hv q hq => h₄ v hv q ?_⟩
      simpa only [if_pos hv] using hq }

theorem rank_le {D : Datum H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) (r z : O) (hr : ((β r : c.F) : ℂ) = H.rt0)
    (hz : ((β z : c.F) : ℂ) = zeta l.A) (τ : 𝓞 E →+* AlgebraicClosure (FractionRing O')) :
    Module.finrank (𝓞 E) a.D₀.X ≤ max D.p D.q := by
  obtain ⟨h, -⟩ := a.geom (AlgebraicClosure (FractionRing O')) r z hr hz _ rfl
  obtain ⟨n, -, hn⟩ := h τ
  split_ifs at hn <;> omega

example {D : Datum H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) :
    D.La → @QkPt O' _ _ a.D₀ (FractionRing O') _ (Algebra.id _) l.M := a.eta

end GlobalTheory.ArcInTest
