import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentCombinationEigenAction
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

noncomputable section

namespace GlobalTheory.FlagEmb

theorem exists_comb_le_iff_sub_mem_span {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (v : Fin n → M) (i : Fin n) (y : M) :
    (∃ cf : Fin n → R, (∀ j, i < j → cf j = 0) ∧ y = ∑ j, cf j • v j) ↔
      ∃ d : R, y - d • v i ∈ Submodule.span R (v '' {j | j < i}) := by
  classical
  have hs : ({j | j < i} : Set (Fin n)) = ↑(Finset.univ.filter (· < i)) := by ext j; simp
  simp_rw [hs, Submodule.mem_span_image_finset_iff_exists_fun', Finset.sum_filter]
  constructor
  · rintro ⟨cf, h0, rfl⟩
    refine ⟨cf i, cf, ?_⟩
    have e : ∀ j, cf j • v j = (if j < i then cf j • v j else 0) + (if j = i then cf i • v i else 0) := by
      intro j
      rcases lt_trichotomy j i with h | h | h
      · simp [h, h.ne]
      · subst h; simp
      · simp [h0 j h, not_lt.2 h.le, h.ne']
    rw [eq_sub_iff_add_eq]
    conv_rhs => rw [Finset.sum_congr rfl fun j _ => e j]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  · rintro ⟨d, g, hg⟩
    refine ⟨fun j => if j < i then g j else if j = i then d else 0, fun j hj => ?_, ?_⟩
    · simp [not_lt.2 hj.le, hj.ne']
    · have e : ∀ j, (if j < i then g j else if j = i then d else 0) • v j =
          (if j < i then g j • v j else 0) + (if j = i then d • v i else 0) := by
        intro j
        rcases lt_trichotomy j i with h | h | h
        · simp [h, h.ne]
        · subst h; simp
        · simp [not_lt.2 h.le, h.ne']
      rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_ite_eq', hg]
      simp

theorem sameFlag_iff_tri_crd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (L : FinLB X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd t L M), IsLieEmb t L aff crd → ∀ (i : Fin L.n) (R : Type) [CommRing R] (φ : Γ(X, L.U i) →+* R) (x : Sp R ⟶ X) (f f' : c.F →+* R) (u u' : Vecs Dw t R), spMap φ ≫ (aff i).fromSpec = x → IsFrame t f x u → IsFrame t f' x u' → (SameFlag (fun τ => Finset.range (Dw.mult τ + 1)) t x u u' ↔ ∃ d, Tri (fun z : Let Dw.mult => crd i R φ (u z.1 z.2)) (fun z => crd i R φ (u' z.1 z.2)) d) ∧ (∀ τ, LinearIndependent R fun j => crd i R φ (u τ j)) ∧ (f = f' → InBlock (fun z : Let Dw.mult => crd i R φ (u z.1 z.2)) (fun z => crd i R φ (u' z.1 z.2))) := by
  intro E _ _ _ H Dw l c X t L aff M crd hL i R _ φ x f f' u u' hx hu hu'
  subst hx
  have htan : ∀ τ j, IsTanAtG t (spMap φ ≫ (aff i).fromSpec) (u τ j) := fun τ j => (hu.1 τ j).1
  have htan' : ∀ τ j, IsTanAtG t (spMap φ ≫ (aff i).fromSpec) (u' τ j) := fun τ j => (hu'.1 τ j).1
  refine ⟨⟨fun hS => ?_, fun ⟨d, hd⟩ => ?_⟩, fun τ => ?_, fun hff => ?_⟩
  · have h : ∀ z : Let Dw.mult, ∃ d : R, crd i R φ (u' z.1 z.2) - d • crd i R φ (u z.1 z.2) ∈
        Submodule.span R ((fun j : Fin (Dw.mult z.1) => crd i R φ (u z.1 j)) '' {j | j < z.2}) := by
      rintro ⟨τ, j⟩
      obtain ⟨cf, hcf0, hcomb⟩ := hS τ (j + 1) (by simp) j (Nat.lt_succ_self _)
      have e := (hL.comb_iff i φ rfl (htan τ) (htan' τ j) cf).1 hcomb
      exact (exists_comb_le_iff_sub_mem_span (fun k => crd i R φ (u τ k)) j _).1
        ⟨cf, fun k hk => hcf0 k (Nat.succ_le_of_lt hk), e⟩
    choose d hd using h
    exact ⟨d, hd⟩
  · intro τ k _ j hjk
    obtain ⟨cf, hcf0, e⟩ := (exists_comb_le_iff_sub_mem_span (fun k => crd i R φ (u τ k)) j _).2 ⟨d ⟨τ, j⟩, hd ⟨τ, j⟩⟩
    refine ⟨cf, fun k' hk' => hcf0 k' (Fin.lt_def.2 (lt_of_lt_of_le hjk hk')), ?_⟩
    exact (hL.comb_iff i φ rfl (htan τ) (htan' τ j) cf).2 e
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨w, hwt, hwc⟩ := exists_comb t (htan τ) g
    obtain ⟨w0, hw0t, hw0c⟩ := exists_comb t (htan τ) 0
    have e1 := (hL.comb_iff i φ rfl (htan τ) hwt g).1 hwc
    have e0 := (hL.comb_iff i φ rfl (htan τ) hw0t 0).1 hw0c
    have hww : w = w0 := hL.inj i R φ w w0 hwt hw0t (by rw [e1, e0, hg]; simp)
    subst hww
    have heig : ∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ w := fun a =>
      (GlobalTheory.FlagEmb.eig_comb_and_frame_cell E H Dw l c X t R _).1 _ (u τ) g w a _ (fun j => ⟨htan τ j, (hu.1 τ j).2 a⟩) hwc
    have := (hu.2 τ w hwt heig).unique hwc hw0c
    intro j
    simpa using congrFun this j
  · subst hff
    intro z
    obtain ⟨a, ha, _⟩ := hu.2 z.1 (u' z.1 z.2) (hu'.1 z.1 z.2).1 (hu'.1 z.1 z.2).2
    have e := (hL.comb_iff i φ rfl (htan z.1) (htan' z.1 z.2) a).1 ha
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨a, e.symm⟩

end GlobalTheory.FlagEmb
