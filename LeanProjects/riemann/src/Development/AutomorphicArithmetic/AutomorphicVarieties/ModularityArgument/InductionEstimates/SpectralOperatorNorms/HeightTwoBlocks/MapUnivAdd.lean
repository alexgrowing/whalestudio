import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.Blo
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.NearBlo
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.ResTyp

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (BW.Pl E)}

private abbrev Pts (E : Type) [Field E] [NumberField E] : Type :=
  ((E →+* ℂ) → Multiset ℂ) → (BW.Pl E → Multiset ℂ) → Prop

private def key {n : ℕ} (d : Dat S n) : ℕ × Pts E := (d.len, d.On)

private def step (S : Set (BW.Pl E)) (r : ℕ) (p : ((E →+* ℂ) → Fin r → ℂ) × (BW.Pl E → Multiset ℂˣ))
    (q : ℕ × Pts E) : ℕ × Pts E :=
  (q.1 + 1, fun Λ t => ∃ (c : ℂ) (Λ' : (E →+* ℂ) → Multiset ℂ) (t' : BW.Pl E → Multiset ℂ), q.2 Λ' t' ∧
    (∀ τ, Λ τ = (Finset.univ.val.map fun i => p.1 τ i + c) + Λ' τ) ∧
    ∀ w ∉ S, t w = ((p.2 w).map fun x : ℂˣ => (x : ℂ) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-c)) + t' w)

open Classical in

private noncomputable def par {r : ℕ} (b : Blo S r) : ((E →+* ℂ) → Fin r → ℂ) × (BW.Pl E → Multiset ℂˣ) :=
  (b.Λ, fun w => if w ∈ S then 0 else b.sat w)

private theorem map_univ_add {α : Type} {r s : ℕ} (f : Fin (r + s) → α) :
    (Finset.univ.val.map f) =
      (Finset.univ.val.map fun i => f (Fin.castAdd s i)) + Finset.univ.val.map fun i => f (Fin.natAdd r i) := by
  have key : ∀ {m : ℕ} (g : Fin m → α), Finset.univ.val.map g = ∑ i, ({g i} : Multiset α) := by
    intro m g
    have e : (Finset.univ.val.map fun i => ({g i} : Multiset α)) =
        (Finset.univ.val.map g).map fun a => ({a} : Multiset α) := by
      rw [Multiset.map_map]
      rfl
    rw [Finset.sum_eq_multiset_sum, e, Multiset.sum_map_singleton]
  rw [key, key, key, Fin.sum_univ_add]

private theorem msOf_cons {r s : ℕ} (b : Blo S r) (d : Dat S s) (z : Fin (d.len + 1) → ℂ) (τ : E →+* ℂ) :
    msOf ((Dat.cons b d).ptL z) τ =
      (Finset.univ.val.map fun i => b.Λ τ i + z 0) + msOf (d.ptL fun j => z j.succ) τ := by
  simp only [msOf]
  rw [map_univ_add]
  congr 1
  · refine Multiset.map_congr rfl fun i _ => ?_
    simp [Dat.ptL, Dat.lam, Dat.idx]
    exact congrArg z (Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _)
  · refine Multiset.map_congr rfl fun i _ => ?_
    simp [Dat.ptL, Dat.lam, Dat.idx]
    exact congrArg z (Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) _)

private theorem ptS_cons {r s : ℕ} (b : Blo S r) (d : Dat S s) (z : Fin (d.len + 1) → ℂ) (w : BW.Pl E) :
    (Dat.cons b d).ptS z w =
      ((b.sat w).map fun x : ℂˣ => (x : ℂ) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-z 0)) + d.ptS (fun j => z j.succ) w := by
  change (∑ j : Fin (d.len + 1), _) = _
  rw [Fin.sum_univ_succ]
  rfl

private theorem step_key {r s : ℕ} (b : Blo S r) (d : Dat S s) :
    step S r (par b) (key d) = key (Dat.cons b d) := by
  refine Prod.ext rfl (funext fun Λ => funext fun t => propext ⟨?_, ?_⟩)
  · rintro ⟨c, Λ', t', ⟨z, rfl, ht'⟩, hΛ, ht⟩
    refine ⟨(Fin.cons c z : Fin (d.len + 1) → ℂ), funext fun τ => ?_, fun w hw => ?_⟩
    · rw [msOf_cons]
      simpa [par] using hΛ τ
    · rw [ptS_cons]
      have := ht w hw
      simp only [par, key, if_neg hw] at this
      rw [this, ht' w hw]
      simp
  · rintro ⟨(z : Fin (d.len + 1) → ℂ), rfl, ht⟩
    refine ⟨z 0, msOf (d.ptL fun j => z j.succ), d.ptS fun j => z j.succ,
      ⟨fun j => z j.succ, rfl, fun _ _ => rfl⟩, fun τ => ?_, fun w hw => ?_⟩
    · rw [msOf_cons]
      rfl
    · rw [ht w hw, ptS_cons]
      simp [par, if_neg hw]

private def Fin' (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (S : Set (BW.Pl E)) (n : ℕ) : Prop :=
  ∀ (ρ : Typ E n) (B : ℝ),
    {q : ℕ × Pts E | ∃ d : Dat S n, d.HasTyp ρ.ρ ∧ (∀ τ i, ‖d.lam τ i‖ ≤ B) ∧ q = key d}.Finite

private theorem fin_cons (r s : ℕ) (hs : Fin' E S s) (ρ : Typ E (r + s)) (B : ℝ) :
    {q : ℕ × Pts E | ∃ (b : Blo S r) (d : Dat S s), (Dat.cons b d).HasTyp ρ.ρ ∧
      (∀ τ i, ‖(Dat.cons b d).lam τ i‖ ≤ B) ∧ q = key (Dat.cons b d)}.Finite := by
  obtain ⟨⟨ρ₁, c₁, e₁⟩, ⟨ρ₂, c₂, e₂⟩, -⟩ := UpperTheory.ConvolutionTheory.BW.resTyp E r s ρ
  have f₁ := UpperTheory.ConvolutionTheory.BW.nearBlo E S r ⟨ρ.d, ρ₁, c₁⟩ B
  have f₂ := hs ⟨ρ.d, ρ₂, c₂⟩ B
  refine (f₁.image2 (step S r) f₂).subset ?_
  rintro q ⟨b, d, ⟨hK, hT⟩, hB, rfl⟩
  refine ⟨par b, ⟨b, ?_, fun τ i => ?_, rfl, fun w => rfl⟩, key d, ⟨d, ?_, fun τ i => ?_, rfl⟩, step_key b d⟩
  · change Killed (⇑ρ₁) b.f.1
    rw [e₁]
    exact hK
  · simpa [Dat.lam] using hB τ (Fin.castAdd s i)
  · change d.HasTyp (⇑ρ₂)
    rw [e₂]
    exact hT
  · simpa [Dat.lam] using hB τ (Fin.natAdd r i)

private theorem dat_cases {n : ℕ} (d : Dat S n) :
    (n = 0 ∧ HEq d (Dat.nil : Dat S 0)) ∨
      ∃ (r s : ℕ) (b : Blo S r) (d' : Dat S s), r + s = n ∧ 0 < r ∧ HEq d (Dat.cons b d') := by
  cases d with
  | nil => exact Or.inl ⟨rfl, HEq.rfl⟩
  | cons b d' => exact Or.inr ⟨_, _, b, d', rfl, b.pos, HEq.rfl⟩

private theorem fin_all (n : ℕ) : Fin' E S n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ρ B
    have A : ∀ r s : ℕ, {q : ℕ × Pts E | r + s = n ∧ 0 < r ∧ ∃ (d : Dat S n) (b : Blo S r) (d' : Dat S s),
        HEq d (Dat.cons b d') ∧ d.HasTyp ρ.ρ ∧ (∀ τ i, ‖d.lam τ i‖ ≤ B) ∧ q = key d}.Finite := by
      intro r s
      by_cases h : r + s = n ∧ 0 < r
      · obtain ⟨h, hr⟩ := h
        subst h
        refine (fin_cons r s (ih s (by omega)) ρ B).subset ?_
        rintro q ⟨-, -, d, b, d', he, h₁, h₂, rfl⟩
        obtain rfl := eq_of_heq he
        exact ⟨b, d', h₁, h₂, rfl⟩
      · exact Set.finite_empty.subset fun q hq => h ⟨hq.1, hq.2.1⟩
    have A₀ : {q : ℕ × Pts E | n = 0 ∧ ∃ d : Dat S n, HEq d (Dat.nil : Dat S 0) ∧ q = key d}.Finite := by
      by_cases h : n = 0
      · subst h
        refine (Set.finite_singleton (key (Dat.nil : Dat S 0))).subset ?_
        rintro q ⟨-, d, he, rfl⟩
        obtain rfl := eq_of_heq he
        rfl
      · exact Set.finite_empty.subset fun q hq => h hq.1
    refine (A₀.union (Set.finite_iUnion fun p : Fin (n + 1) × Fin (n + 1) => A p.1 p.2)).subset ?_
    rintro q ⟨d, h₁, h₂, rfl⟩
    rcases dat_cases d with ⟨h, he⟩ | ⟨r, s, b, d', h, hr, he⟩
    · exact Or.inl ⟨h, d, he, rfl⟩
    · refine Or.inr (Set.mem_iUnion.2 ⟨(⟨r, by omega⟩, ⟨s, by omega⟩), h, hr, d, b, d', he, h₁, h₂, rfl⟩)

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.near2 :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (S : Set (BW.Pl E)) (n : ℕ) (ρ : Typ E n) (B : ℝ), ∃ D : Set (Dat S n), D.Finite ∧
      ∀ d : Dat S n, d.HasTyp ρ.ρ → (∀ τ i, ‖d.lam τ i‖ ≤ B) → ∃ d' ∈ D, d'.len = d.len ∧ ∀ Λ t, d'.On Λ t ↔ d.On Λ t := by
  intro E _ _ _ S n ρ B
  have f := fin_all (E := E) (S := S) n ρ B
  have := f.to_subtype
  choose g hg using fun q : {q : ℕ × Pts E | ∃ d : Dat S n, d.HasTyp ρ.ρ ∧ (∀ τ i, ‖d.lam τ i‖ ≤ B) ∧ q = key d} => q.2
  refine ⟨Set.range g, Set.finite_range g, fun d h₁ h₂ => ?_⟩
  have e : key d = key (g ⟨key d, d, h₁, h₂, rfl⟩) := (hg ⟨key d, d, h₁, h₂, rfl⟩).2.2
  refine ⟨_, ⟨_, rfl⟩, (congrArg Prod.fst e).symm, fun Λ t => ?_⟩
  have e₂ : d.On = (g ⟨key d, d, h₁, h₂, rfl⟩).On := congrArg Prod.snd e
  rw [← e₂]
