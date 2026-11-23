import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsThetaLatticeCorrespondenceWeilOperatorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationThetaMovedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosureStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WeilInter

variable {D : D7} {N N' : ℕ}

theorem sd_of_moves {g : GA D N} {L : Lat D N} (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  have : L = Lt g := by
    ext x; rw [h x, (h1 g).1 x]
  rw [this]; exact (h1 g).2

theorem klat (T : Tor D) {g : GA D N} {g' : GA D N'} {L : Lat D N} {L' : Lat D N'}
    (h : Moves D (g : GL (Fin N) (AE D)) L) (h' : Moves D (g' : GL (Fin N') (AE D)) L') :
    KLat D T (La D T L L') := Or.inr ⟨_, _, sd_of_moves h, sd_of_moves h', rfl⟩

theorem quot_bijective {V : Type} [AddCommGroup V] (A₁ A₂ B₁ B₂ : AddSubgroup V) (f : B₁ → B₂)
    (h1 : ∀ x y : B₁, (x : V) - (y : V) ∈ A₁ ↔ (f x : V) - (f y : V) ∈ A₂)
    (h2 : ∀ y : B₂, ∃ x : B₁, (f x : V) - (y : V) ∈ A₂) :
    Function.Bijective (fun q : B₁ ⧸ A₁.addSubgroupOf B₁ =>
      (QuotientAddGroup.mk (f (Quotient.out q)) : B₂ ⧸ A₂.addSubgroupOf B₂)) := by
  have e1 : ∀ x y : B₁, (QuotientAddGroup.mk x : B₁ ⧸ A₁.addSubgroupOf B₁) = QuotientAddGroup.mk y ↔
      (x : V) - (y : V) ∈ A₁ := fun x y => by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]; rfl
  have e2 : ∀ x y : B₂, (QuotientAddGroup.mk x : B₂ ⧸ A₂.addSubgroupOf B₂) = QuotientAddGroup.mk y ↔
      (x : V) - (y : V) ∈ A₂ := fun x y => by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]; rfl
  constructor
  · intro q q' hq
    have := (e1 _ _).2 ((h1 _ _).2 ((e2 _ _).1 hq))
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
  · intro r
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective r
    obtain ⟨x, hx⟩ := h2 y
    refine ⟨QuotientAddGroup.mk x, ?_⟩
    have h3 := (h1 _ _).1 ((e1 (Quotient.out (QuotientAddGroup.mk x : B₁ ⧸ A₁.addSubgroupOf B₁)) x).1
      (QuotientAddGroup.out_eq' _))
    refine (e2 _ _).2 ?_
    have := A₂.add_mem h3 hx
    rwa [sub_add_sub_cancel] at this

theorem wd_congr {T : Tor D} {A B : AddSubgroup (VC D N N')} (hA : Nice D T A) (hB : Nice D T B)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T A) {u v : VC D N N'} (hu : u ∈ B) (hv : v ∈ B) (h : u - v ∈ A) :
    Wd D T u G = Wd D T v G := by
  have h1 := Wd_Wd D T v (u - v) G
  rw [((hA.mem_ThSp G).1 hG).2 _ h, hB.2.1 v hv _ (B.sub_mem hu hv), one_smul, add_sub_cancel] at h1
  exact h1.symm

theorem iop_sum {T : Tor D} (A : AddSubgroup (VC D N N')) {B : AddSubgroup (VC D N N')} (hB : Nice D T B)
    [Fintype (B ⧸ A.addSubgroupOf B)] (F : VC D N N' → ℂ) :
    Iop D T A B F = ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) •
      ∑ q : B ⧸ A.addSubgroupOf B, Wd D T ((Quotient.out q : B) : VC D N N') F := by
  rw [hB.Iop_eq]
  funext z
  rw [finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

theorem zero_mem_TT (T : Tor D) : (0 : VC D N N' → ℂ) ∈ TT D T N N' := by
  refine ⟨differentiable_const _, 1, Nat.one_pos, fun x _ => ?_⟩
  have := Wd_smul D T (1 • x) 0 (0 : VC D N N' → ℂ)
  rwa [zero_smul, zero_smul] at this

theorem om_sum {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0)
    (hadd : ∀ F ∈ TT D (tor0 D cc δ) N N', ∀ G ∈ TT D (tor0 D cc δ) N N', F + G ∈ TT D (tor0 D cc δ) N N')
    (g : GA D N) (g' : GA D N') {ι : Type} (s : Finset ι) (φ : ι → VC D N N' → ℂ)
    (hφ : ∀ i, φ i ∈ TT D (tor0 D cc δ) N N') :
    ∑ i ∈ s, φ i ∈ TT D (tor0 D cc δ) N N' ∧ W.Om g g' (∑ i ∈ s, φ i) = ∑ i ∈ s, W.Om g g' (φ i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    refine ⟨zero_mem_TT _, ?_⟩
    have := W.smul g g' 0 0 (zero_mem_TT _)
    rwa [zero_smul, zero_smul] at this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨hadd _ (hφ a) _ ih.1, by rw [W.add g g' _ (hφ a) _ ih.1, ih.2]⟩

theorem om_iop : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → δ ≠ 0 → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h k : GA D N) (g' h' k' : GA D N') (L₁ L₂ M₁ M₂ : Lat D N) (L₁' L₂' M₁' M₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → Moves D (k : GL (Fin N) (AE D)) M₁ → Moves D (k' : GL (Fin N') (AE D)) M₁' → Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) M₂ → Moves D ((g' * k' : GA D N') : GL (Fin N') (AE D)) M₂' → ∀ F ∈ Th D (tor0 D cc δ) L₁ L₁', W.Om g g' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) M₁ M₁') F) = Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₂ L₂') (La D (tor0 D cc δ) M₂ M₂') (W.Om g g' F) := by
  intro D cc δ hc hδ N N' e0 W g h k g' h' k' L₁ L₂ M₁ M₂ L₁' L₂' M₁' M₂' a1 a1' a2 a2' b1 b1' b2 b2' F hF
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.T.thetaFunctions_all_levels_closure D cc δ hc N N'
  have hFT := t1 _ _ (sd_of_moves a1) (sd_of_moves a1') F hF
  have hG := GlobalTheory.T.weilRepresentation_theta_moved_lattice D cc δ hc N N' e0 W g h g' h' L₁ L₂ L₁' L₂' a1 a1' a2 a2' F hF
  obtain ⟨f, f1, f2, f3⟩ := GlobalTheory.T.exists_thetaLattice_correspondence_weilOperator D cc δ hc hδ N N' e0 W g h k g' h' k' L₁ L₂ M₁ M₂ L₁' L₂' M₁' M₂'
    a1 a1' a2 a2' b1 b1' b2 b2' F hFT
  have kA1 := klat (tor0 D cc δ) a1 a1'
  have kA2 := klat (tor0 D cc δ) a2 a2'
  have kB1 := klat (tor0 D cc δ) b1 b1'
  have kB2 := klat (tor0 D cc δ) b2 b2'
  have nA2 := GlobalTheory.ThetaTriple.nice_of_klat hc kA2
  have nB1 := GlobalTheory.ThetaTriple.nice_of_klat hc kB1
  have nB2 := GlobalTheory.ThetaTriple.nice_of_klat hc kB2
  haveI i1 := AddSubgroup.fintypeOfIndexNeZero (GlobalTheory.ThetaTriple.index_ne_zero hc kA1 kB1)
  haveI i2 := AddSubgroup.fintypeOfIndexNeZero (GlobalTheory.ThetaTriple.index_ne_zero hc kA2 kB2)
  have hb := quot_bijective _ _ _ _ f f2 f3
  have hi : ((La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) M₁ M₁')).index =
      ((La D (tor0 D cc δ) L₂ L₂').addSubgroupOf (La D (tor0 D cc δ) M₂ M₂')).index :=
    Nat.card_congr (Equiv.ofBijective _ hb)
  have hW : ∀ x : La D (tor0 D cc δ) M₁ M₁', Wd D (tor0 D cc δ) (x : VC D N N') F ∈ TT D (tor0 D cc δ) N N' := by
    intro x
    obtain ⟨z, hz, -⟩ := exists_pt_of_mem_La_moved D (GlobalTheory.InducedType.induced_type D).1 cc δ hc.1.1 N N' k k'
      M₁ M₁' b1 b1' x x.2
    rw [hz]
    exact t2 z F hFT
  obtain ⟨s1, s2⟩ := om_sum W t3 g g' Finset.univ
    (fun q : La D (tor0 D cc δ) M₁ M₁' ⧸ (La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) M₁ M₁') =>
      Wd D (tor0 D cc δ) ((Quotient.out q : La D (tor0 D cc δ) M₁ M₁') : VC D N N') F) (fun q => hW _)
  rw [iop_sum _ nB1, iop_sum _ nB2, W.smul g g' _ _ s1, s2, hi]
  congr 1
  refine Fintype.sum_bijective _ hb _ _ fun q => ?_
  rw [f1]
  refine wd_congr nA2 nB2 hG (f _).2 (Subtype.property _) ?_
  have := (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (f (Quotient.out q)) : La D (tor0 D cc δ) M₂ M₂' ⧸
    (La D (tor0 D cc δ) L₂ L₂').addSubgroupOf (La D (tor0 D cc δ) M₂ M₂'))).symm
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf] at this
  exact this

end GlobalTheory.WeilInter
