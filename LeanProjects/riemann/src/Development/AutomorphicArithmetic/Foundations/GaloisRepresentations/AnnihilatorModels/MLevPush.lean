import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.UPel.HT.EtLev

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}
  {s : S ⟶ Sp R}

private theorem act_add' (o : Obj b N s) {T : Over S} (g : T ⟶ o.A) (a a' : 𝓞 D.F) :
    g ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a + a')) =
      (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) * (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a')) := by
  rw [map_add, o.act.add, MonObj.comp_mul]

private theorem act_mul' (o : Obj b N s) {T : Over S} (g : T ⟶ o.A) (a a' : 𝓞 D.F) :
    g ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a * a')) =
      (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := by
  rw [map_mul, o.act.mul, Category.assoc]

private theorem act_one' (o : Obj b N s) {T : Over S} (g : T ⟶ o.A) :
    g ≫ o.act.act (algebraMap (𝓞 D.F) D.O 1) = g := by
  rw [map_one, o.act.one, Category.comp_id]

private theorem act_nat (o : Obj b N s) {T : Over S} (g : T ⟶ o.A) (n : ℕ) :
    g ≫ o.act.act (algebraMap (𝓞 D.F) D.O (n : 𝓞 D.F)) = g ^ n := by
  induction n with
  | zero =>
    have h := act_add' o g 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.mp h
  | succ n ih =>
    rw [Nat.cast_succ, act_add', ih, act_one', pow_succ]

private theorem eq_one_of_killed (o : Obj b N s) {I J : Ideal (𝓞 D.F)} (h : I ⊔ J = ⊤) {T : Over S} {g : T ⟶ o.A}
    (hI : KilledBy o I g) (hJ : KilledBy o J g) : g = 1 := by
  have h1 : (1 : 𝓞 D.F) ∈ I ⊔ J := h ▸ Submodule.mem_top
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h1
  rw [← act_one' o g, ← hij, act_add', hI i hi, hJ j hj, _root_.mul_one]

private theorem exists_pow_eq (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {c : ℕ} (hc : 0 < c)
    {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (g : Over.mk x ⟶ A) :
    ∃ v : Over.mk x ⟶ A, v ^ c = g := by
  obtain ⟨hfin, -, hsurj⟩ := GlobalTheory.KthRoot.finite_flat_surjective_mulN_any S A hA c hc
  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (pullback.fst g.left (mulN A c).left)
  have hsq : pullback.fst g.left (mulN A c).left ≫ g.left = pullback.snd g.left (mulN A c).left ≫ (mulN A c).left :=
    pullback.condition
  have hw : (t ≫ pullback.snd g.left (mulN A c).left) ≫ A.hom = x := by
    have e1 := Over.w (mulN A c)
    have e2 := Over.w g
    calc (t ≫ pullback.snd g.left (mulN A c).left) ≫ A.hom
        = t ≫ pullback.snd g.left (mulN A c).left ≫ (mulN A c).left ≫ A.hom := by rw [e1, Category.assoc]
      _ = t ≫ pullback.fst g.left (mulN A c).left ≫ g.left ≫ A.hom := by
          rw [← Category.assoc (pullback.snd _ _), ← hsq, Category.assoc]
      _ = x := by rw [e2, ← Category.assoc, ht, Category.id_comp]; rfl
  refine ⟨Over.homMk (t ≫ pullback.snd g.left (mulN A c).left) hw, ?_⟩
  rw [← Category.comp_id (Over.homMk _ hw), ← MonObj.comp_pow, ← GlobalTheory.MulFlatSurj.mulN_eq_pow]
  ext1
  simp only [Over.comp_left, Over.homMk_left, Category.assoc]
  rw [← hsq, ← Category.assoc, ht]
  exact Category.id_comp _

end

theorem levPush_of : IdealSplit → LevPush := by
  intro hsplit p _ D R _ b N r w 𝔞 ρ hcop he S s c o o' ψ hψ hker lv hlv
  obtain ⟨e, he⟩ := he
  have hc : 0 < c := hψ.pos
  obtain ⟨-, hmon, hcomm, -, -, ψ', hmon', h1, h2⟩ := hψ
  obtain ⟨hadd, hlin, hwsub, hgeom⟩ := hlv
  have hcopρ : 𝔞 ^ ρ ⊔ w = ⊤ := by
    rw [sup_comm]
    exact Ideal.sup_pow_eq_top (by rw [sup_comm]; exact hcop)
  have hle : uIdeal D r ^ (e * ρ) ≤ 𝔞 ^ ρ := by
    rw [pow_mul]
    exact Ideal.pow_right_mono he ρ
  have hlvK : ∀ y, KilledBy o (𝔞 ^ ρ) (lv y) := by
    intro y a ha
    rw [← hlin]
    exact hwsub _ (Submodule.subset_span ⟨a, ha, y, rfl⟩)
  have hfix : ∀ {X : Over S} (oo : GlobalTheory.UPel.HT.Obj b N s) (g : X ⟶ oo.A) (β : 𝓞 D.F), β - 1 ∈ 𝔞 ^ ρ →
      KilledBy oo (𝔞 ^ ρ) g → g ≫ oo.act.act (algebraMap (𝓞 D.F) D.O β) = g := by
    intro X oo g β hβ hg
    have h3 := act_add' oo g (β - 1) 1
    rw [sub_add_cancel] at h3
    rw [h3, hg _ hβ, act_one', _root_.one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp only
    rw [hadd, MonObj.mul_comp]
  · intro c' x
    dsimp only
    rw [hlin, Category.assoc, hcomm, Category.assoc]
  · intro x hx
    dsimp only
    rw [hwsub x hx, MonObj.one_comp]
  · intro kk _ _ xx
    obtain ⟨hinj, hsurj⟩ := hgeom kk xx
    constructor
    · intro y hy
      apply hinj y
      have hI : KilledBy o (𝔞 ^ ρ) (toUnit (Over.mk xx) ≫ lv y) := by
        intro a ha
        rw [Category.assoc, hlvK y a ha, MonObj.comp_one]
      have hJ : KilledBy o w (toUnit (Over.mk xx) ≫ lv y) := by
        refine hker _ _ ⟨?_, e * ρ, fun a ha => hI a (hle ha)⟩
        rw [Category.assoc]
        exact hy
      exact eq_one_of_killed o hcopρ hI hJ
    · intro g' hg'
      obtain ⟨u0, hu0⟩ := exists_pow_eq o'.A o'.ab hc xx g'
      have hpre : (u0 ≫ ψ') ≫ ψ = g' := by
        rw [Category.assoc, h2, MonObj.comp_pow, Category.comp_id, hu0]
      have hkill : ∀ {X : Over S} (z : X ⟶ o.A), z ≫ ψ = 1 → z ^ c = 1 := by
        intro X z hz
        rw [← Category.comp_id z, ← MonObj.comp_pow, ← h1, ← Category.assoc, hz, MonObj.one_comp]
      have hc0 : ((c : ℕ) : 𝓞 D.F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      obtain ⟨m, α, hα1, hαm⟩ := hsplit (𝓞 D.F) (uIdeal D r) (c : 𝓞 D.F) hc0 (e * ρ)
      have h1top : (1 : 𝓞 D.F) ∈ 𝔞 ^ ρ ⊔ w := hcopρ ▸ Submodule.mem_top
      obtain ⟨v, hv, u, hu, hvu⟩ := Submodule.mem_sup.mp h1top
      set h0 := u0 ≫ ψ' with hh0
      have hA : ∀ a ∈ 𝔞 ^ ρ, (h0 ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ ψ = 1 := by
        intro a ha
        rw [Category.assoc, hcomm, ← Category.assoc, hpre]
        exact hg' a ha
      have hB : ∀ a ∈ 𝔞 ^ ρ, KilledBy o w ((h0 ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫
          o.act.act (algebraMap (𝓞 D.F) D.O α)) := by
        intro a ha
        refine hker _ _ ⟨?_, m, ?_⟩
        · haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O α)
          rw [Category.assoc, hcomm, ← Category.assoc, hA a ha, MonObj.one_comp]
        · intro bb hbb
          obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hαm bb hbb)
          rw [← act_mul', ← act_mul']
          have hre : bb * α * a = t * ((c : 𝓞 D.F) * a) := by linear_combination (-a) * ht
          rw [hre, act_mul', act_mul', act_nat, hkill _ (hA a ha)]
          haveI := o.act.hom (algebraMap (𝓞 D.F) D.O t)
          exact MonObj.one_comp _
      have hK : KilledBy o (𝔞 ^ ρ) ((h0 ≫ o.act.act (algebraMap (𝓞 D.F) D.O α)) ≫
          o.act.act (algebraMap (𝓞 D.F) D.O u)) := by
        intro a ha
        rw [← act_mul', ← act_mul', show a * u * α = u * (α * a) by ring, act_mul', act_mul']
        exact hB a ha u hu
      obtain ⟨y, hy⟩ := hsurj _ hK
      refine ⟨y, ?_⟩
      dsimp only
      rw [← Category.assoc, hy, Category.assoc, hcomm, ← Category.assoc, Category.assoc h0, hcomm,
        ← Category.assoc, hpre]
      have hα' : α - 1 ∈ 𝔞 ^ ρ := hle hα1
      have hu' : u - 1 ∈ 𝔞 ^ ρ := by
        have : u - 1 = -v := by linear_combination hvu
        rw [this]
        exact (𝔞 ^ ρ).neg_mem hv
      rw [hfix o' g' α hα' hg', hfix o' g' u hu' hg']

end UpperTheory.Gal.crystallineComparison.Mod
