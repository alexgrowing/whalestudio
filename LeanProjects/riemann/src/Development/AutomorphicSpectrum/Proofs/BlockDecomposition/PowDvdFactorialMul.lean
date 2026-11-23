import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapMemExt

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickLine

theorem pow_dvd_factorial_mul {p : ℕ} (hp : p.Prime) (N : ℕ) : p ^ N ∣ (p * N).factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, pow_succ]
    exact (mul_dvd_mul ih (Nat.dvd_factorial hp.pos le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem isNilpotent_of_mem {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) {p : ℕ} (hp : p.Prime)
    (hn : IsNilpotent (p : A)) {x : A} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hn
  obtain ⟨k, hk⟩ := pow_dvd_factorial_mul hp N
  refine ⟨p * N, ?_⟩
  rw [← δ.factorial_mul_dpow_eq_pow hx, hk]
  push_cast
  rw [hN]
  simp

theorem ringHom_eq {B C : Type} [CommRing B] [CommRing C] (Q : PDPoly B) {f g : Q.P →+* C}
    (h1 : ∀ b, f (algebraMap B Q.P b) = g (algebraMap B Q.P b)) (h2 : ∀ k, f (Q.e k) = g (Q.e k)) : f = g := by
  ext p
  have hp : p ∈ Submodule.span B (Set.range Q.e) := Q.e.mem_span p
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h2 k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul b x _ hx => rw [Algebra.smul_def, map_mul, map_mul, hx, h1]

theorem e_one_mem {B : Type} [CommRing B] (Q : PDPoly B) (J : Ideal B) : Q.e 1 ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem le_comap_ext {B : Type} [CommRing B] (Q : PDPoly B) (J : Ideal B) :
    J ≤ (Q.ext J).comap (algebraMap B Q.P) :=
  fun _ hx => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem s_eq_one (T : Thick (F.cr b ht κ)) : T.s = 1 := by
  have h : (1 : T.B) = T.s * T.i b.t := (Finset.prod_of_isEmpty (ι := Empty) _).symm.trans T.hs
  rw [ht, map_one, mul_one] at h
  exact Units.ext h.symm

variable (T : Thick (F.cr b ht κ)) (Q : PDPoly T.B) (η₀ : DividedPowers (Q.ext T.J)) (hη : Q.IsStd T.δ η₀)
  (hp : b.p ≠ 0)

def line : Thick (F.cr b ht κ) where
  B := Q.P
  i := (algebraMap T.B Q.P).comp T.i
  J := Q.ext T.J
  δ := η₀
  adm := ⟨fun _ => by simpa using (T.adm.1 hp).map (algebraMap T.B Q.P), fun h => absurd h hp⟩
  compat := IsDPMorphism.comp _ hη.dp T.compat
  α := ()
  y := (F.cr b ht κ).Pt.map
    (CommRingCat.ofHom (Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J))) T.y
  inα := trivial
  w r := by
    change Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J)
      ((F.cr b ht κ).str T.y (Ideal.Quotient.mk _ r)) = _
    rw [T.w r]
    rfl
  x j := j.elim
  v j := j.elim
  s := 1
  hx j := j.elim
  hs := (Finset.prod_of_isEmpty (ι := Empty) _).trans (by rw [ht]; simp)
  hv := (map_one _).trans (Finset.prod_of_isEmpty (ι := Empty) _).symm

def toLine : T ⟶ line T Q η₀ hη hp where
  φ := algebraMap T.B Q.P
  u j := j.elim
  comm _ := rfl
  dp := hη.dp
  hle := le_comap_ext Q T.J
  pt := rfl
  hx j := j.elim
  hs := by
    rw [s_eq_one T, map_one, mul_one]
    exact (Finset.prod_of_isEmpty (ι := Empty) _).symm
  hv j := j.elim

variable {T Q η₀ hη hp}

theorem exists_ext {T' : Thick (F.cr b ht κ)} (φ : T ⟶ T') {c : T'.B} (hc : c ∈ T'.J) :
    ∃ ψ : line T Q η₀ hη hp ⟶ T', toLine T Q η₀ hη hp ≫ ψ = φ ∧ ψ.φ (Q.e 1) = c := by
  obtain ⟨G, hG1, hG2⟩ := FubiniStudyChowHeightFormula₂.Adr.Fil.exists_lift Q T'.B φ.φ (fun k => T'.δ.dpow k c) (T'.δ.dpow_zero hc) (fun m k => T'.δ.mul_dpow hc)
  have hGa : G.comp (algebraMap T.B Q.P) = φ.φ := RingHom.ext hG1
  have hGdp : IsDPMorphism η₀ T'.δ G :=
    FubiniStudyChowHeightFormula₂.Adr.dp_of_std T.δ Q η₀ hη T'.δ G c hc (by rw [hGa]; exact φ.dp) hG2
  have hle : Q.ext T.J ≤ T'.J.comap G := Ideal.map_le_iff_le_comap.1 hGdp.1
  refine ⟨{ φ := G, u := fun j => j.elim, comm := fun r => ?_, dp := hGdp, hle := hle, pt := ?_,
            hx := fun j => j.elim, hs := ?_, hv := fun j => j.elim }, ?_, ?_⟩
  · exact (hG1 _).trans (φ.comm r)
  · refine Eq.trans ?_ φ.pt
    have e : CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle) =
        CommRingCat.ofHom (Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J)) ≫
          CommRingCat.ofHom (Ideal.quotientMap T'.J G hle) := by
      refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      change Ideal.Quotient.mk T'.J (φ.φ a) = Ideal.Quotient.mk T'.J (G (algebraMap T.B Q.P a))
      rw [hG1]
    rw [e, Functor.map_comp]
    rfl
  · rw [s_eq_one T']
    refine Units.ext ?_
    change (1 : T'.B) = ((∏ j : Empty, (j.elim : T'.Bˣ)) * Units.map G.toMonoidHom 1 : T'.Bˣ)
    simp
  · exact Thick.Hom.ext hGa (funext fun j => j.elim)
  · change G (Q.e 1) = c
    rw [hG2 1]
    exact T'.δ.dpow_one hc

theorem hom_unique {T' : Thick (F.cr b ht κ)} {ψ ψ' : line T Q η₀ hη hp ⟶ T'}
    (h : toLine T Q η₀ hη hp ≫ ψ = toLine T Q η₀ hη hp ≫ ψ') (he : ψ.φ (Q.e 1) = ψ'.φ (Q.e 1)) : ψ = ψ' := by
  refine Thick.Hom.ext (ringHom_eq Q (fun a => ?_) fun k => ?_) (funext fun j => j.elim)
  · exact congrArg (fun f : T ⟶ T' => f.φ a) h
  · have h1 : T'.δ.dpow k (ψ.φ (Q.e 1)) = ψ.φ (η₀.dpow k (Q.e 1)) := ψ.dp.2 (Q.e 1) (e_one_mem Q T.J)
    have h2 : T'.δ.dpow k (ψ'.φ (Q.e 1)) = ψ'.φ (η₀.dpow k (Q.e 1)) := ψ'.dp.2 (Q.e 1) (e_one_mem Q T.J)
    rw [hη.var k] at h1 h2
    have h3 : T'.δ.dpow k (ψ.φ (Q.e 1)) = T'.δ.dpow k (ψ'.φ (Q.e 1)) := congrArg _ he
    exact h1.symm.trans (h3.trans h2)

def lineU (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (hpp : b.p.Prime) :
    (thU (F.cr b ht κ) q hq).U (line T Q η₀ hη hpp.ne_zero) :=
  ⟨(isNilpotent_of_mem η₀ hpp (by simpa using (T.adm.1 hpp.ne_zero).map (algebraMap T.B Q.P))
      (e_one_mem Q T.J)).isUnit_one_add.unit,
    MonoidHom.mem_ker.2 (Units.ext (by
      change Ideal.Quotient.mk (Q.ext T.J) (1 + Q.e 1) = Ideal.Quotient.mk (Q.ext T.J) 1
      exact Ideal.Quotient.eq.2 (by simpa using e_one_mem Q T.J)))⟩

theorem map_lineU {T' : Thick (F.cr b ht κ)} (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (hpp : b.p.Prime)
    (ψ : line T Q η₀ hη hpp.ne_zero ⟶ T') :
    ((((thU (F.cr b ht κ) q hq).map ψ (lineU q hq hpp)).1 : T'.Bˣ) : T'.B) = 1 + ψ.φ (Q.e 1) := by
  change (ψ.φ : Q.P →+* T'.B) ((1 : Q.P) + Q.e 1) = 1 + _
  exact (map_add (ψ.φ : Q.P →+* T'.B) 1 (Q.e 1)).trans (by rw [map_one]; rfl)

theorem main : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ) (hμ : c μ ∈ b.I) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (x : b.R), b.p.Prime → (q : b.R) = x ^ b.p → c μ = q - 1 → (∑ i ∈ Finset.range b.p, x ^ i) ∈ b.I → ∀ T : Thick (F.cr b ht κ), ∃ (T₁ : Thick (F.cr b ht κ)) (i : T ⟶ T₁) (η : (thU (F.cr b ht κ) q hq).U T₁), (∀ (T' : Thick (F.cr b ht κ)) (φ : T ⟶ T') (a : (thU (F.cr b ht κ) q hq).U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ (thU (F.cr b ht κ) q hq).map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → (thU (F.cr b ht κ) q hq).map g η = (thU (F.cr b ht κ) q hq).q _ * η → (pdFlt (F.cr b ht κ) c ρ hρ μ hμ).FAcyc i g := by
  intro O _ F b ht κ Λ _ c ρ hρ μ hμ q hq x hpp hqx hcμ hsum T
  have hp0 := hpp.ne_zero
  obtain ⟨Q⟩ : Nonempty (PDPoly T.B) := ⟨GlobalTheory.PDA.Model.pdPoly T.B⟩
  obtain ⟨η₀, hη⟩ := FubiniStudyChowHeightFormula₂.Adr.exists_std T.B T.J T.δ Q
  refine ⟨line T Q η₀ hη hp0, toLine T Q η₀ hη hp0, lineU q hq hpp, ?_, ?_⟩
  · intro T' φ a
    have hc : ((a.1 : T'.Bˣ) : T'.B) - 1 ∈ T'.J := by
      have h : Ideal.Quotient.mk T'.J ((a.1 : T'.Bˣ) : T'.B) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 a.2)
      exact Ideal.Quotient.eq.1 (h.trans (map_one _).symm) |> fun h => by simpa using h
    obtain ⟨ψ, h1, h2⟩ := exists_ext (Q := Q) (η₀ := η₀) (hη := hη) (hp := hp0) φ hc
    refine ⟨ψ, ⟨h1, ?_⟩, ?_⟩
    · refine Subtype.ext (Units.ext ?_)
      refine (map_lineU q hq hpp ψ).trans ?_
      rw [h2]
      ring
    · rintro ψ' ⟨h1', h2'⟩
      have e : 1 + ψ'.φ (Q.e 1) = ((a.1 : T'.Bˣ) : T'.B) := (map_lineU q hq hpp ψ').symm.trans
        (congrArg (fun u : (thU (F.cr b ht κ) q hq).U T' => ((u.1 : T'.Bˣ) : T'.B)) h2')
      refine hom_unique (h1'.trans h1.symm) ?_
      rw [h2]
      exact eq_sub_of_add_eq' e
  · intro g hg hgη
    let gφ : Q.P →+* Q.P := g.φ
    have hgφ : gφ.comp (algebraMap T.B Q.P) = algebraMap T.B Q.P :=
      congrArg (fun f : T ⟶ line T Q η₀ hη hp0 => f.φ) hg
    have hmul : gφ (1 + Q.e 1) = algebraMap T.B Q.P ((T.i x) ^ b.p) * (1 + Q.e 1) := by
      have e : gφ (1 + Q.e 1) = algebraMap T.B Q.P (T.i (q : b.R)) * (1 + Q.e 1) :=
        congrArg (fun u : (thU (F.cr b ht κ) q hq).U (line T Q η₀ hη hp0) =>
          ((u.1 : (line T Q η₀ hη hp0).Bˣ) : (line T Q η₀ hη hp0).B)) hgη
      rw [e, hqx, map_pow]
    have hsum' : (∑ i ∈ Finset.range b.p, (T.i x) ^ i) ∈ T.J := by
      have := T.i_mem hsum
      simpa [map_sum, map_pow] using this
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.CompanionTheory.PDAcyc.main T.δ Q η₀ hη b.p hpp (T.adm.1 hp0) (T.i x) hsum' gφ hgφ g.dp hmul
    have hμ' : ∀ z : Q.P, algebraMap T.B Q.P ((T.i x) ^ b.p - 1) * z =
        algebraMap T.B Q.P (T.i (c μ)) * z := by
      intro z
      rw [hcμ, hqx, map_sub T.i, map_pow, map_one]
    refine ⟨h1, ?_, ?_⟩
    · intro r z hz hz'
      obtain ⟨m, hm, e⟩ := h2 (ρ r) z hz hz'
      exact ⟨m, T.pdPow_anti (hρ.2 r) hm, e.trans (hμ' z)⟩
    · intro r z hz
      obtain ⟨y, hy, e⟩ := h3 (ρ r) z hz
      exact ⟨y, (line T Q η₀ hη hp0).pdPow_anti (hρ.2 r) hy, e.trans (hμ' z)⟩

end GlobalTheory.CompanionTheory.ThickLine
