import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.RankZero

theorem eq_zero_of_half_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [hd : DiscreteTopology Λ]
    (h : ∀ z ∈ Λ, (2⁻¹ : ℝ) • z ∈ Λ) (z : Fin g → ℂ) (hz : z ∈ Λ) : z = 0 := by
  have hn : ∀ n : ℕ, ((2⁻¹ : ℝ) ^ n) • z ∈ Λ := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih => rw [pow_succ', mul_smul]; exact h _ ih
  have ht : Filter.Tendsto (fun n : ℕ => ((2⁻¹ : ℝ) ^ n) • z) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)).smul_const z
    simpa using this
  have ht' : Filter.Tendsto (fun n : ℕ => (⟨_, hn n⟩ : Λ)) Filter.atTop (nhds 0) :=
    tendsto_subtype_rng.2 ht
  rw [nhds_discrete, Filter.tendsto_pure] at ht'
  obtain ⟨n, hn'⟩ := ht'.exists
  have h0 : ((2⁻¹ : ℝ) ^ n) • z = 0 := congrArg Subtype.val hn'
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 (by positivity)
  · exact h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem subsingleton_lattice (D : Datum H) (hD : D.p + D.q = 0) : Subsingleton D.La := by
  haveI := D.fin
  haveI := D.proj
  by_contra hne
  have hnt : Nontrivial D.La := not_subsingleton_iff_nontrivial.1 hne
  have := (Module.finrank_pos_iff (R := 𝓞 E) (M := D.La)).2 hnt
  rw [D.rank, hD] at this
  exact lt_irrefl _ this

theorem subsingleton_unif {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {s : Sp ℂ ⟶ Sp B}
    (hD : D.p + D.q = 0) (o : Obj D l b s) {g : ℕ} (u : HolUnif o.t.G o.t.PP.L g) :
    Subsingleton (Fin g → ℂ) := by
  haveI := subsingleton_lattice D hD
  obtain ⟨-, I, -⟩ := o.geom ℂ (𝟙 _) (Spec.preimage s).hom (by simp [spMap])
  have h1 : I.ev 2 0 = 1 := (I.ker 2 two_pos 0).2 ⟨0, Subsingleton.elim _ _⟩
  have htor : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x * x = 1 → x = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := (I.onto 2 two_pos x).1 (by rw [pow_two]; exact hx)
    rw [Subsingleton.elim a 0, h1] at ha
    exact ha.symm
  haveI := u.discrete
  have hΛ : ∀ z ∈ u.Λ, z = 0 := by
    refine eq_zero_of_half_mem u.Λ (fun z hz => (u.ker _).1 (htor _ ?_))
    rw [← u.ex_add, ← add_smul, u.ker]
    norm_num
    exact hz
  refine subsingleton_of_forall_eq 0 (fun z => ?_)
  have hz : z ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) := by rw [u.full]; trivial
  have : Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) = ⊥ := Submodule.span_eq_bot.2 hΛ
  rwa [this, Submodule.mem_bot] at hz

theorem hasTransport_of_rank_zero (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l)
    (U : Set (Xo.XF c)) (e : c.F →+* ℂ) (hD : D.p + D.q = 0) : HasTransport Xo c U e := by
  intro y y' _ _ _ _ o o' _ _ g g' u u' Hm Hm' κ κ' _ _
  haveI := subsingleton_unif hD o u
  haveI := subsingleton_unif hD o' u'
  haveI : Subsingleton (𝟙_ (Over (Sp ℂ)) ⟶ o'.t.G) := u'.ex_onto.subsingleton
  refine ⟨LinearEquiv.ofSubsingleton _ _, fun z => ?_, fun _ _ _ _ => Subsingleton.elim _ _, fun z w => ?_,
    fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  · rw [Subsingleton.elim z 0, map_zero]
    simp
  · rw [Subsingleton.elim z 0, map_zero]
    simp [HermitianCompactForm.herm]

end GlobalTheory.DetLine.RankZero
