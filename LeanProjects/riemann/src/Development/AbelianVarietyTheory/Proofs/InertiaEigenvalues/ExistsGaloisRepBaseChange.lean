import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightLocalisationRegularAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepMultisetJumpsStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.GalIsoBC

def Good (D : D7) (i : D.nd.Loc) (r : ℕ) (p : ∀ w, D.naut.LP w)
    (m : (D.host.E →+* ℂ) → Multiset ℂ) : Prop :=
  ∃ ρ : GE D.nd →* GL (Fin r) (Qbar (D.nd.l i)), (SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧
    (∀ w, D.naut.wdOf i ρ w = p w) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧
      ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) =
        m ((D.naut.iotaQC i).toRingHom.comp τ))

theorem good_congr {D : D7} {i : D.nd.Loc} {r r' : ℕ} {p p' : ∀ w, D.naut.LP w}
    {m m' : (D.host.E →+* ℂ) → Multiset ℂ} (hr : r = r') (hp : ∀ w, p w = p' w) (hm : ∀ τ, m τ = m' τ)
    (h : Good D i r p m) : Good D i r' p' m' := by
  subst hr
  have e1 : p = p' := funext hp
  have e2 : m = m' := funext hm
  subst e1; subst e2; exact h

theorem good_sum {D : D7} (h0 : SumRepresentations.tie0 D) {i : D.nd.Loc} {a b : ℕ} {p q : ∀ w, D.naut.LP w}
    {m m' : (D.host.E →+* ℂ) → Multiset ℂ} (ha : Good D i a p m) (hb : Good D i b q m') :
    Good D i (a + b) (fun w => D.naut.lpSum (p w) (q w)) (fun τ => m τ + m' τ) := by
  obtain ⟨ρ, hρ⟩ := ha
  obtain ⟨ρ', hρ'⟩ := hb
  exact GlobalTheory.T.galois_rep_multiset_jumps D h0 i a b ρ ρ' p q m m' hρ hρ'

theorem good_fold {D : D7} (h0 : SumRepresentations.tie0 D) {i : D.nd.Loc} {β : Type*} (r : β → ℕ)
    (f : β → ∀ w, D.naut.LP w) (g : β → (D.host.E →+* ℂ) → Multiset ℂ) :
    ∀ L : List β, L ≠ [] → (∀ x ∈ L, Good D i (r x) (f x) (g x)) →
      Good D i (L.map r).sum (fun w => L.foldr (fun x acc => D.naut.lpSum (f x w) acc) (D.naut.lpZero w))
        (fun τ => (L.map fun x => g x τ).sum)
  | [], h, _ => (h rfl).elim
  | [x], _, hx => by
      refine good_congr ?_ ?_ ?_ (hx x (List.mem_singleton_self x))
      · simp
      · intro w; simp [D.naut.lpSum_zero]
      · intro τ; simp
  | x :: y :: L, _, hx => by
      have ih := good_fold h0 r f g (y :: L) (List.cons_ne_nil _ _)
        (fun z hz => hx z (List.mem_cons_of_mem _ hz))
      have := good_sum h0 (hx x List.mem_cons_self) ih
      refine good_congr ?_ ?_ ?_ this
      · simp only [List.map_cons, List.sum_cons]
      · intro w; simp only [List.foldr_cons]
      · intro τ; simp only [List.map_cons, List.sum_cons]

theorem lpTw_lpZero (D : D7) (w : PlE D.host) (s : ℝ) : D.naut.lpTw (D.naut.lpZero w) s = D.naut.lpZero w := by
  have hu : D.naut.unr (D.naut.lpTw (D.naut.lpZero w) s) := (D.naut.unr_tw _ s).2 (D.naut.lpZero_unr w)
  have e3 : D.naut.frobEig (D.naut.lpTw (D.naut.lpZero w) s) = D.naut.frobEig (D.naut.lpZero w) := by
    rw [D.naut.frobEig_tw _ s (D.naut.lpZero_unr w), D.naut.frobEig_zero]; simp
  rw [D.naut.unr_eq_lpUnr _ hu, e3, ← D.naut.unr_eq_lpUnr _ (D.naut.lpZero_unr w)]

theorem lpTw_foldr (D : D7) (w : PlE D.host) {β : Type*} (f : β → D.naut.LP w) (s : ℝ) :
    ∀ L : List β, D.naut.lpTw (L.foldr (fun x acc => D.naut.lpSum (f x) acc) (D.naut.lpZero w)) s =
      L.foldr (fun x acc => D.naut.lpSum (D.naut.lpTw (f x) s) acc) (D.naut.lpZero w)
  | [] => lpTw_lpZero D w s
  | x :: L => by
      simp only [List.foldr_cons]
      rw [D.naut.lpTw_sum, lpTw_foldr D w f s L]

theorem map_list_sum {α γ : Type*} (h : α → γ) :
    ∀ L : List (Multiset α), L.sum.map h = (L.map fun x => x.map h).sum
  | [] => by simp
  | x :: L => by simp [Multiset.map_add, map_list_sum h L]

theorem le_list_sum {α : Type*} {x : Multiset α} : ∀ {L : List (Multiset α)}, x ∈ L → x ≤ L.sum
  | [], hx => by simp at hx
  | y :: L, hx => by
      rw [List.sum_cons]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Multiset.le_add_right _ _
      · exact le_trans (le_list_sum hx) (Multiset.le_add_left _ _)

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

theorem flatMap_single {γ : Type*} (f : ℕ → γ) : ∀ l : List ℕ, List.flatMap (fun a => [f a]) l = l.map f
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, flatMap_single f l]

theorem spehLoc_eq (D : D7) (p : Formalism.BasicNotions.Part D.naut.CG) (w : PlE D.host) :
    spehLoc D.nd D.naut p w = (List.range p.d).foldr (fun (k : ℕ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - (k : ℝ))) acc) (D.naut.lpZero w) := by
  unfold spehLoc
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℝ)), List.foldr_map]

theorem isoInf_eq (D : D7) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut Pa τ = (Pa.map fun p => ((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum).sum := by
  unfold isoInf
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℂ)), List.map_map]
  rfl

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

theorem good_part (D : D7) (h0 : SumRepresentations.tie0 D) (h2 : SumRepresentations.adm2 D) (i : D.nd.Loc) (P : D.naut.AV i)
    (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (hinf : ∀ τ, isoInf D.nd D.naut Pa τ = D.naut.infWt i τ)
    (p : Formalism.BasicNotions.Part D.naut.CG) (hp : p ∈ Pa) (ha : 1 ≤ p.a) (hd : 1 ≤ p.d) (hc : D.naut.csd p.π) :
    Good D i (p.a * p.d) (fun w => D.naut.lpTw (spehLoc D.nd D.naut p w) ((1 - (D.R.nV : ℝ)) / 2))
      (fun τ => (((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum).map
          (fun z => -z + ((D.R.nV : ℂ) - 1) / 2)) := by
  have hreg := GlobalTheory.T.infWt_nodup_and_half_integral D i P
  set e : ℕ → ℤ := fun k => (p.d : ℤ) - 2 * k - D.R.nV with he
  have hne : List.range p.d ≠ [] := by
    rw [Ne, List.range_eq_nil]; omega
  have hpiece : ∀ k ∈ List.range p.d, Good D i p.a (fun w => D.naut.lpTw (D.naut.locG p.π w) ((e k : ℝ) / 2))
      (fun τ => (D.naut.infG p.π τ).map (fun z => -(z + (e k : ℂ) / 2))) := by
    intro k hk
    refine GlobalTheory.T.exists_galois_rep_twist D h0 h2 i p.a ha p.π (e k) hc ?_
    intro τ
    have hS : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ))) ≤ D.naut.infWt i τ := by
      rw [← hinf τ, isoInf_eq]
      refine le_trans (le_list_sum (List.mem_map_of_mem (f := fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))) hk)) ?_
      exact le_list_sum (List.mem_map_of_mem (f := fun p : Formalism.BasicNotions.Part D.naut.CG => ((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum) hp)
    refine ⟨Multiset.Nodup.of_map _ (Multiset.nodup_of_le hS (hreg τ).1), ?_⟩
    intro z hz
    obtain ⟨m, hm⟩ := (hreg τ).2 _ (Multiset.mem_of_le hS (Multiset.mem_map_of_mem _ hz))
    refine ⟨m, ?_⟩
    have hm' : z = (m : ℂ) + ((D.R.nV : ℂ) - 1) / 2 - (((p.d : ℂ) - 1) / 2 - k) := by
      rw [← hm]; ring
    rw [hm', he]; push_cast; ring
  have hf := good_fold h0 (fun _ : ℕ => p.a)
    (fun k w => D.naut.lpTw (D.naut.locG p.π w) ((e k : ℝ) / 2))
    (fun k τ => (D.naut.infG p.π τ).map (fun z => -(z + (e k : ℂ) / 2))) (List.range p.d) hne hpiece
  refine good_congr ?_ ?_ ?_ hf
  · simp [mul_comm]
  · intro w
    have h1 := lpTw_foldr D w (fun k : ℕ => D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - (k : ℝ)))
      ((1 - (D.R.nV : ℝ)) / 2) (List.range p.d)
    beta_reduce at h1
    rw [spehLoc_eq, h1]
    congr 1
    funext k acc
    rw [D.naut.lpTw_add, he]
    congr 2
    push_cast; ring
  · intro τ
    rw [map_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply, Multiset.map_map]
    congr 1
    funext z
    simp only [Function.comp_apply, he]
    push_cast; ring

theorem galRep_isobaric : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → ∀ (i : D.nd.Loc) (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)), IsBCV D.nd D.naut i P Pa → ∃ ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), (SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = (D.naut.infWt i ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -z + ((D.R.nV : ℂ) - 1) / 2)) := by
  intro D h0 h2 i P Pa hB
  obtain ⟨hparts, -, hrank, -, -, hinf⟩ := hB
  have hne : Pa ≠ [] := by
    rintro rfl
    have ht := D.R.t_odd.pos
    simp [rankIso, Ranks.nV] at hrank
    omega
  have hf := good_fold h0 (fun p : Formalism.BasicNotions.Part D.naut.CG => p.a * p.d)
    (fun p w => D.naut.lpTw (spehLoc D.nd D.naut p w) ((1 - (D.R.nV : ℝ)) / 2))
    (fun p τ => (((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum).map
          (fun z => -z + ((D.R.nV : ℂ) - 1) / 2)) Pa hne
    (fun p hp => good_part D h0 h2 i P Pa hinf p hp (hparts p hp).1 (hparts p hp).2.1 (hparts p hp).2.2)
  have hg : Good D i D.R.nV (fun w => D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))
      (fun τ => (D.naut.infWt i τ).map (fun z => -z + ((D.R.nV : ℂ) - 1) / 2)) := by
    refine good_congr ?_ ?_ ?_ hf
    · exact hrank
    · intro w
      exact (lpTw_foldr D w (fun p : Formalism.BasicNotions.Part D.naut.CG => spehLoc D.nd D.naut p w) _ Pa).symm
    · intro τ
      rw [← hinf τ, isoInf_eq, map_list_sum, List.map_map]
      rfl
  exact hg

end GlobalTheory.GalIsoBC
