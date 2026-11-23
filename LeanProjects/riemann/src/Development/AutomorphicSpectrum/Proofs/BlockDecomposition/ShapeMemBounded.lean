import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.F.F5

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FinFamAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Cov (S : Set (Pre E n)) : Prop :=
  ∃ (k : ℕ) (D : Fin k → Pre E n), ∀ D' ∈ S, ∃ j, PreEquiv (D j) D'

theorem cov_of_rel {S : Set (Pre E n)} {ι : Type*} [Finite ι] (P : ι → Pre E n → Prop)
    (h1 : ∀ D ∈ S, ∃ a, P a D)
    (h2 : ∀ a, ∀ D₁ ∈ S, ∀ D₂ ∈ S, P a D₁ → P a D₂ → PreEquiv D₁ D₂) : Cov S := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨D₀, -⟩ := hS
    let e := Finite.equivFin ι
    refine ⟨Nat.card ι, fun j => if h : ∃ D ∈ S, P (e.symm j) D then h.choose else D₀, ?_⟩
    intro D' hD'
    obtain ⟨a, ha⟩ := h1 D' hD'
    have hex : ∃ D ∈ S, P (e.symm (e a)) D := ⟨D', hD', by rw [Equiv.symm_apply_apply]; exact ha⟩
    refine ⟨e a, ?_⟩
    show PreEquiv (if h : ∃ D ∈ S, P (e.symm (e a)) D then h.choose else D₀) D'
    rw [dif_pos hex]
    obtain ⟨hmem, hP⟩ := hex.choose_spec
    exact h2 _ _ hmem _ hD' hP (by rw [Equiv.symm_apply_apply]; exact ha)
  · exact ⟨0, Fin.elim0, fun D' hD' => (hS ⟨D', hD'⟩).elim⟩

theorem cov_of_cover {S : Set (Pre E n)} {ι : Type*} [Finite ι] (A : ι → Set (Pre E n))
    (hA : ∀ a, Cov (A a)) (hS : ∀ D ∈ S, ∃ a, D ∈ A a) : Cov S := by
  classical
  choose k D hD using fun a => (hA a : ∃ (k : ℕ) (D : Fin k → Pre E n), ∀ D' ∈ A a, ∃ j, PreEquiv (D j) D')
  let e := Finite.equivFin (Σ a, Fin (k a))
  refine ⟨Nat.card (Σ a, Fin (k a)), fun j => D (e.symm j).1 (e.symm j).2, ?_⟩
  intro D' hD'
  obtain ⟨a, ha⟩ := hS D' hD'
  obtain ⟨j, hj⟩ := hD a D' ha
  refine ⟨e ⟨a, j⟩, ?_⟩
  show PreEquiv (D (e.symm (e ⟨a, j⟩)).1 (e.symm (e ⟨a, j⟩)).2) D'
  rw [Equiv.symm_apply_apply]
  exact hj

abbrev Shape (E : Type) [Field E] : Type :=
  Σ c : ℕ, (Fin c → ℕ) × (Fin c → (E →+* ℂ) → Multiset ℂ)

def shape (D : Pre E n) : Shape E := ⟨D.c, D.N, D.m⟩

def bounded (E : Type) [Field E] (n : ℕ) (m : (E →+* ℂ) → Multiset ℂ) : Set (Shape E) :=
  {t | t.1 ≤ n ∧ (∀ i, t.2.1 i ≤ n) ∧ ∀ i τ, t.2.2 i τ ≤ m τ}

theorem finite_le (s : Multiset ℂ) : {x : Multiset ℂ | x ≤ s}.Finite := by
  exact (Multiset.finite_toSet s.powerset).subset fun x hx => Multiset.mem_powerset.mpr hx

theorem bounded_finite (n : ℕ) (m : (E →+* ℂ) → Multiset ℂ) : (bounded E n m).Finite := by
  refine ((Set.finite_Iic n).biUnion fun c _ =>
    (((Set.Finite.pi fun _ : Fin c => Set.finite_Iic n).prod
      (Set.Finite.pi fun _ : Fin c => Set.Finite.pi fun τ => finite_le (m τ))).image
        (fun p => (⟨c, p⟩ : Shape E)))).subset ?_
  rintro ⟨c, N, mm⟩ ⟨hc, hN, hm⟩
  exact Set.mem_iUnion₂.mpr ⟨c, hc, ⟨(N, mm), ⟨fun i _ => hN i, fun i _ τ _ => hm i τ⟩, rfl⟩⟩

theorem shape_mem_bounded (m : (E →+* ℂ) → Multiset ℂ) (D : Pre E n)
    (hm : ∀ τ, ∑ i, D.m i τ = m τ) : shape D ∈ bounded E n m := by
  refine ⟨?_, fun i => ?_, fun i τ => ?_⟩
  · show D.c ≤ n
    calc D.c = ∑ _i : Fin D.c, 1 := by simp
      _ ≤ ∑ i, D.N i := Finset.sum_le_sum fun i _ => D.pos i
      _ = n := D.h
  · show D.N i ≤ n
    exact (Finset.single_le_sum (f := D.N) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans D.h.le
  · show D.m i τ ≤ m τ
    rw [← hm τ]
    exact Finset.single_le_sum (f := fun j => D.m j τ) (fun j _ => Multiset.zero_le _) (Finset.mem_univ i)

theorem cov_fibre (hL : LevelFactor) (hF : FinDiscN)
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (hK : IsLevel K) (hW : ∀ N, FiniteDimensional ℂ (W N))
    (t : Shape E) :
    Cov {D' : Pre E n | shape D' = t ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)} := by
  classical
  obtain ⟨c, N, mm⟩ := t
  by_cases hsum : ∑ i, N i = n
  swap
  · refine ⟨0, Fin.elim0, ?_⟩
    rintro ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ ⟨hsh, -, -⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hsh
    obtain ⟨rfl, -⟩ := Prod.mk.inj (eq_of_heq hh)
    exact absurd h' hsum
  choose Ki hKiopen hKiKGL hKisph using fun w => hL E w c n N hsum (K w) (hK.1 w)
  have hlev : ∀ i : Fin c, IsLevel (fun w => Ki w i) := fun i =>
    ⟨fun w => hKiopen w i, hK.2.mono fun w hw => hKiKGL w hw i⟩
  choose k σs hσs using fun i : Fin c =>
    hF E (N i) (fun w => Ki w i) (W (N i)) (mm i) (hlev i) (hW (N i))
  refine cov_of_rel (ι := (i : Fin c) → Fin (k i))
    (fun a D => ∃ hc : D.c = c, ∀ (i : Fin D.c) w, ∃ hs hi,
      D.cls i w = GlobalTheory.LocGL.IrrGL.of (σs (Fin.cast hc i) (a (Fin.cast hc i)) w).ρ hs hi) ?_ ?_
  · rintro ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ ⟨hsh, hsph, hKt⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hsh
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh)
    choose a ha using fun i => hσs i (V' i) (fun w => σ' i w) (disc' i) (fun w => loc' i w)
      (fun τ => inf' i τ) (fun w => hKisph w (fun j => σ' j w) (hsph w) i) (hKt i)
    exact ⟨a, rfl, fun i w => ⟨_, _, (ha i w).symm⟩⟩
  · rintro a ⟨c₁, N₁, h₁, V₁, σ₁, m₁, pos₁, disc₁, loc₁, inf₁⟩ ⟨hsh₁, -, -⟩
      ⟨c₂, N₂, h₂, V₂, σ₂, m₂, pos₂, disc₂, loc₂, inf₂⟩ ⟨hsh₂, -, -⟩ ⟨hc₁, hP₁⟩ ⟨hc₂, hP₂⟩
    obtain ⟨rfl, hh₁⟩ := Sigma.mk.inj_iff.mp hsh₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh₁)
    obtain ⟨rfl, hh₂⟩ := Sigma.mk.inj_iff.mp hsh₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh₂)
    refine ⟨finCongr rfl, fun i w => ?_, fun i τ => rfl⟩
    obtain ⟨hs₁, hi₁, e₁⟩ := hP₁ i w
    obtain ⟨hs₂, hi₂, e₂⟩ := hP₂ i w
    exact e₁.trans e₂.symm

theorem finFamOf : FinFamOf := by
  intro hL hF E _ _ _ n K W m hK hW
  have hS : Cov {D' : Pre E n | (∀ τ, ∑ i, D'.m i τ = m τ) ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)} := by
    have hfin := bounded_finite (E := E) n m
    haveI := hfin.to_subtype
    refine cov_of_cover (ι := bounded E n m) (fun t => {D' : Pre E n | shape D' = t.1 ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)}) (fun t => cov_fibre hL hF K W hK hW t.1) ?_
    rintro D' ⟨hm, hsph, hKt⟩
    exact ⟨⟨shape D', shape_mem_bounded m D' hm⟩, rfl, hsph, hKt⟩
  obtain ⟨k, D, hD⟩ := hS
  exact ⟨k, D, fun D' hm hsph hKt => hD D' ⟨hm, hsph, hKt⟩⟩

end GlobalTheory.CompanionTheory.FinFamAssembly

end
