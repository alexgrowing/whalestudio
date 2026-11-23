import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.IdealB
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.IdealStmt

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Id

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes WithZero
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Idele
open Formalism.L2.Host (IsUnitAt IsUnifAt atFin unif unif_spec)
open FractionalIdeal (count)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem lines {B : Base F E} (hB : B.IsGood σ) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {H : Plane E n n₁} {H' : Plane E d d₁} {r s r' s' i j i' j' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (h : H.IsAdapted σ B X X₁ i j) (h' : H'.IsAdapted σ B W W₁ i' j') (hσ : ∀ x, σ (σ x) = x) :
    (Line X.L H.x H.𝔟 ∧ Line X.L H.y (1 * (cj hσ H.𝔟)⁻¹)) ∧
      Line W.L H'.x H'.𝔟 ∧ Line W.L H'.y (codiff E * (cj hσ H'.𝔟)⁻¹) :=
  ⟨plane_lines hσ (ε := 1) (mul_one 1) (fun a b => by rw [hX.herm, one_mul]) hX.lat (fun y => by
      rw [hX.dual]
      refine forall₂_congr fun x _ => ?_
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨fun e => ⟨⟨_, e⟩, rfl⟩, fun ⟨o, e⟩ => e ▸ RingOfIntegers.isIntegral_coe o⟩) one_ne_zero h,
    plane_lines hσ (ε := -1) (by ring) (fun a b => by rw [hW.skew, neg_one_mul]) hW.lat (fun y => by
      rw [hW.dual]
      exact forall₂_congr fun x _ => inD_iff _) codiff_ne_zero h'⟩

theorem memA {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {H : Plane E n n₁} {H' : Plane E d d₁} {𝔭 𝔮 : FI E}
    (a : Line X.L H.x 𝔭) (b : Line W.L H'.y 𝔮) (v : Pl F) (l : (AE F E)ˣ) :
    idem F v • shiftA H H' l ∈ latAtV X W v ↔ InAt (𝔭 * 𝔮) v (l : AE F E) := by
  rw [shiftA, ← smul_assoc, line_lat a b, lat_iff (mul_ne_zero a.ne b.ne)]

theorem memB (hσ : ∀ x, σ (σ x) = x) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {H : Plane E n n₁} {H' : Plane E d d₁}
    {𝔭 𝔮 : FI E} (a : Line X.L H.y 𝔭) (b : Line W.L H'.x 𝔮) (v : Pl F) (l : (AE F E)ˣ) :
    idem F v • shiftB σ H H' l ∈ latAtV X W v ↔ InAt (cj hσ (𝔭 * 𝔮)) v (l : AE F E) := by
  rw [shiftB, ← smul_assoc, line_lat a b, lat_iff (mul_ne_zero a.ne b.ne), inAt_cj_iff hσ (mul_ne_zero a.ne b.ne)]

theorem idealId0 : IdealId0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i j i' j' hB hX hW h h' u hu
  have hσ := PositivityTheory.ThK.Vac.sigma_sigma hB.cm
  obtain ⟨⟨a, a'⟩, b, b'⟩ := lines hB hX hW h h' hσ
  rcases hu with rfl | rfl
  · exact ⟨_, mul_ne_zero a.ne b'.ne, memA a b'⟩
  · exact ⟨_, cj_ne hσ (mul_ne_zero a'.ne b.ne), memB hσ a' b⟩

theorem idealId' : IdealId' := by
  refine ⟨1, 1, -1, -1, ?_⟩
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' r s r' s' i j i' j' hB hX hW h h' hi hj hi' hj' u e₁ e₂ hu
  have hσ := PositivityTheory.ThK.Vac.sigma_sigma hB.cm
  obtain ⟨⟨a, a'⟩, b, b'⟩ := lines hB hX hW h h' hσ
  have pD := pr_codiff hB
  have p1 : Pr B.P (1 : FI E) := fun w _ => FractionalIdeal.count_one _ _
  have pa := plane_pr hσ hB.cm one_ne_zero p1 hX.bas h hi hj ⟨a, a'⟩
  have pb := plane_pr hσ hB.cm codiff_ne_zero pD hW.bas h' hi' hj' ⟨b, b'⟩
  have ca := cj_ne hσ a.ne
  have cb := cj_ne hσ b.ne
  have tr : ∀ ν : Chr F E, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range ν 0 →
      ∀ x : (AF F)ˣ, ν (ideleMap F E x) = 1 := fun ν hν x => hν.triv_of_even Even.zero x
  rcases hu with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · refine ⟨_, mul_ne_zero a.ne b'.ne, memA a b',
      pa.mul a.ne b'.ne (pD.mul codiff_ne_zero (inv_ne_zero cb) (pb.cj hσ hB.cm b.ne).inv), fun ν _ hν hu => ?_⟩
    rw [idealVal_mul _ a.ne b'.ne, idealVal_mul _ codiff_ne_zero (inv_ne_zero cb), idealVal_inv,
      idealVal_cj hσ b.ne pb hu (nu_conj hB.cm (tr ν hν)), idealVal_codiff hB (tr ν hν) hu]
    simp
  · have pp : Pr B.P (1 * (cj hσ H.𝔟)⁻¹ * H'.𝔟) :=
      (p1.mul (one_ne_zero (α := FI E)) (inv_ne_zero ca) (pa.cj hσ hB.cm a.ne).inv).mul a'.ne b.ne pb
    refine ⟨_, cj_ne hσ (mul_ne_zero a'.ne b.ne), memB hσ a' b, pp.cj hσ hB.cm (mul_ne_zero a'.ne b.ne), fun ν _ hν hu => ?_⟩
    rw [idealVal_cj hσ (mul_ne_zero a'.ne b.ne) pp hu (nu_conj hB.cm (tr ν hν)), idealVal_mul _ a'.ne b.ne, one_mul, idealVal_inv,
      idealVal_cj hσ a.ne pa hu (nu_conj hB.cm (tr ν hν))]
    simp [mul_comm]

end PositivityTheory.ThKG.Loc.Cone.Id

end
