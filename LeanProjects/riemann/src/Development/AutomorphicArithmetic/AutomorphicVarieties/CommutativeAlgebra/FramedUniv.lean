import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section
variable {O : Type} [CommRing O] [IsLocalRing O]

private theorem map_max {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    (f : R →ₐ[O] R') {x : R} (hx : x ∈ maximalIdeal R) : f x ∈ maximalIdeal R' := by
  rwa [← res_eq_zero_iff O, res_map f, res_eq_zero_iff]

private theorem quot_univ {A K : Type} [CommRing A] [Algebra O A] [IsCO O A] [CommRing K] [Algebra O K] [Nontrivial K]
    (I : Ideal A) (f0 : A →ₐ[O] K) (h0 : ∀ x ∈ I, f0 x = 0) :
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra O A') (_ : IsCO O A') (p : A →ₐ[O] A'), (∀ x ∈ I, p x = 0) ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] (f : A →ₐ[O] R'), (∀ x ∈ I, f x = 0) →
        ∃! g : A' →ₐ[O] R', g.comp p = f := by
  have hne : I ≠ ⊤ := fun e => by
    have := h0 1 (e ▸ Submodule.mem_top)
    simp at this
  haveI := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsCO O (A ⧸ I) := co_quot O A _ (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  refine ⟨A ⧸ I, inferInstance, inferInstance, inferInstance, Ideal.Quotient.mkₐ O I,
    fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 hx, fun R' _ _ f hf => ⟨Ideal.Quotient.liftₐ I f hf, rfl, fun g hg => ?_⟩⟩
  refine Ideal.Quotient.algHom_ext _ ?_
  rw [hg]
  rfl

private theorem pres [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    (A : Type) [CommRing A] [Algebra O A] [IsCO O A] :
    ∃ (n : ℕ) (π : MvPowerSeries (Fin n) O →ₐ[O] A), Function.Surjective π := by
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (maximalIdeal A))
  have ham : ∀ s, a s ∈ maximalIdeal A := fun s => ha ▸ Submodule.subset_span ⟨s, rfl⟩
  haveI := co_mvps O O (Fin n)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := co_ev O O A (Fin n) (Algebra.ofId O A) a ham
  refine ⟨n, F, co_surj O _ A F (le_trans ?_ le_sup_left)⟩
  rw [← ha, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  rw [← hF]
  refine Ideal.mem_map_of_mem _ ?_
  intro hu
  have := MvPowerSeries.isUnit_iff_constantCoeff.1 hu
  simp at this

private theorem X_mem {R σ : Type} [CommRing R] [IsLocalRing R] (s : σ) :
    (X s : MvPowerSeries σ R) ∈ maximalIdeal (MvPowerSeries σ R) := by
  intro hu
  have := MvPowerSeries.isUnit_iff_constantCoeff.1 hu
  simp at this

private noncomputable def Ca (O : Type) [CommRing O] (σ R : Type) [CommRing R] [Algebra O R] : R →ₐ[O] MvPowerSeries σ R :=
  IsScalarTower.toAlgHom O R (MvPowerSeries σ R)

private theorem coprod2 [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    (A B : Type) [CommRing A] [Algebra O A] [IsCO O A] [CommRing B] [Algebra O B] [IsCO O B] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (_ : IsCO O S) (j : A →ₐ[O] S) (i : B →ₐ[O] S),
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (j' : A →ₐ[O] R') (i' : B →ₐ[O] R'),
        ∃! f : S →ₐ[O] R', f.comp j = j' ∧ f.comp i = i' := by
  obtain ⟨n, π, hπ⟩ := pres (O := O) A
  haveI := co_mvps O O (Fin n)
  haveI := co_mvps O B (Fin n)
  haveI := (co_res O).1
  obtain ⟨e, ⟨-, he⟩, -⟩ := co_ev O O (MvPowerSeries (Fin n) B) (Fin n) (Algebra.ofId O _) X X_mem
  have ext0 : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (F G : MvPowerSeries (Fin n) O →ₐ[O] R'),
      (∀ s, F (X s) = G (X s)) → F = G := fun R' _ _ _ F G h =>
    (co_ev O O R' (Fin n) (Algebra.ofId O _) (fun s => G (X s)) fun s => map_max G (X_mem s)).unique
      ⟨F.commutes, h⟩ ⟨G.commutes, fun _ => rfl⟩
  have key : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (j' : A →ₐ[O] R') (i' : B →ₐ[O] R'),
      ∃! F : MvPowerSeries (Fin n) B →ₐ[O] R', F.comp e = j'.comp π ∧ F.comp (Ca O _ B) = i' := by
    intro R' _ _ _ j' i'
    obtain ⟨F, ⟨h1, h2⟩, h3⟩ := co_ev O B R' (Fin n) i' (fun s => j' (π (X s)))
      fun s => map_max (j'.comp π) (X_mem s)
    refine ⟨F, ⟨ext0 _ _ _ fun s => by simp [he, h2], AlgHom.ext h1⟩, fun G hG => h3 G ⟨fun x => ?_, fun s => ?_⟩⟩
    · exact DFunLike.congr_fun hG.2 x
    · rw [← he]
      exact DFunLike.congr_fun hG.1 (X s)
  have kill : ∀ (R' : Type) [CommRing R'] [Algebra O R'] (j' : A →ₐ[O] R') (F : MvPowerSeries (Fin n) B →ₐ[O] R'),
      F.comp e = j'.comp π → ∀ x ∈ (RingHom.ker π).map e, F x = 0 := by
    intro R' _ _ j' F hF
    refine Ideal.map_le_iff_le_comap (K := RingHom.ker F).2 fun x hx => ?_
    show F (e x) = 0
    rw [show F (e x) = j' (π x) from DFunLike.congr_fun hF x, show π x = 0 from hx, map_zero]
  obtain ⟨F0, ⟨hF0, -⟩, -⟩ := key _ (res O A) (res O B)
  obtain ⟨S, _, _, _, p, hp, hS⟩ := quot_univ _ F0 (kill _ _ _ hF0)
  have H : RingHom.ker π.toRingHom ≤ RingHom.ker (p.comp e).toRingHom := fun x hx => hp _ (Ideal.mem_map_of_mem _ hx)
  let j : A →ₐ[O] S := AlgHom.liftOfSurjective π hπ (p.comp e) H
  have hj : j.comp π = p.comp e := AlgHom.ext fun x => AlgHom.liftOfSurjective_apply π hπ (p.comp e) H x
  refine ⟨S, inferInstance, inferInstance, inferInstance, j, p.comp (Ca O _ B), fun R' _ _ _ j' i' => ?_⟩
  obtain ⟨F, ⟨h1, h2⟩, h3⟩ := key R' j' i'
  obtain ⟨g, hg, hg'⟩ := hS R' F (kill _ _ _ h1)
  refine ⟨g, ⟨(AlgHom.cancel_right hπ).1 ?_, ?_⟩, fun g' h' => hg' g' (h3 _ ⟨?_, h'.2⟩)⟩
  · rw [AlgHom.comp_assoc, hj, ← AlgHom.comp_assoc, hg, h1]
  · rw [← AlgHom.comp_assoc, hg, h2]
  · rw [AlgHom.comp_assoc, ← hj, ← AlgHom.comp_assoc, h'.1]

end

section
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R]

private def Cut (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    (P : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop) : Prop :=
  ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'),
    P R' f ↔ ∀ x ∈ I, f x = 0

private theorem Cut.eq (x y : R) : Cut O R fun _ _ _ _ f => f x = f y :=
  ⟨Ideal.span {x - y}, fun R' _ _ _ f => by
    constructor
    · intro h z hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      simp [h]
    · intro h
      have := h _ (Ideal.mem_span_singleton_self _)
      rwa [map_sub, sub_eq_zero] at this⟩

private theorem Cut.all {κ : Sort*} {P : κ → ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop}
    (h : ∀ i, Cut O R (P i)) : Cut O R fun R' _ _ _ f => ∀ i, P i R' f := by
  choose I hI using h
  refine ⟨⨆ i, I i, fun R' _ _ _ f => ?_⟩
  simp only [hI]
  exact (iSup_le_iff (f := I) (a := RingHom.ker f)).symm

private theorem Cut.and {P Q : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop}
    (h : Cut O R P) (h' : Cut O R Q) : Cut O R fun R' _ _ _ f => P R' f ∧ Q R' f := by
  obtain ⟨I, hI⟩ := h
  obtain ⟨J, hJ⟩ := h'
  refine ⟨I ⊔ J, fun R' _ _ _ f => ?_⟩
  simp only [hI, hJ]
  exact (sup_le_iff (a := I) (b := J) (c := RingHom.ker f)).symm

private theorem Cut.congr {P Q : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop}
    (h : Cut O R P) (e : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), Q R' f ↔ P R' f) :
    Cut O R Q := by
  obtain ⟨I, hI⟩ := h
  exact ⟨I, fun R' _ _ _ f => (e R' f).trans (hI R' f)⟩

private theorem Cut.mat {ι : Type} (x y : Matrix ι ι R) : Cut O R fun _ _ _ _ f => x.map f = y.map f :=
  (Cut.all fun a => Cut.all fun b => Cut.eq (x a b) (y a b)).congr fun _ _ _ _ _ => Matrix.ext_iff.symm

private theorem Cut.univ [IsCO O R] {P : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop}
    (h : Cut O R P) {K : Type} [CommRing K] [Algebra O K] [IsCO O K] (f0 : R →ₐ[O] K) (h0 : P K f0) :
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra O A') (_ : IsCO O A') (p : R →ₐ[O] A'), P A' p ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), P R' f →
        ∃! g : A' →ₐ[O] R', g.comp p = f := by
  obtain ⟨I, hI⟩ := h
  obtain ⟨A', _, _, _, p, hp, hA⟩ := quot_univ I f0 ((hI K f0).1 h0)
  exact ⟨A', inferInstance, inferInstance, inferInstance, p, (hI A' p).2 hp,
    fun R' _ _ _ f hf => hA R' f ((hI R' f).1 hf)⟩

variable {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] {w : ι → X} (Φ : FormData O w) [IsCO O R]

omit [IsLocalRing O] [IsCO O R] in
private theorem map_alg {R' : Type} [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (M : Matrix ι ι O) :
    (M.map (algebraMap O R)).map f = M.map (algebraMap O R') := Matrix.ext fun _ _ => f.commutes _

omit [IsLocalRing O] [IsCO O R] in
private theorem mmul {R' : Type} [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (M N : Matrix ι ι R) :
    (M * N).map f = M.map f * N.map f := Matrix.map_mul

omit [IsLocalRing O] [IsCO O R] in
private theorem mone {R' : Type} [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') :
    (1 : Matrix ι ι R).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)

private theorem cut_HH (h : Matrix ι ι R) (hh : h.map (res O R) = 1) :
    Cut O R fun _ _ _ _ f => Φ.HH (h.map f) := by
  refine ((Cut.mat (h.transpose * Φ.JR R * h) (Φ.JR R)).and (Cut.all fun a => Cut.all fun b =>
    Cut.all fun (_ : Φ.blk a ≠ Φ.blk b) => Cut.eq (h a b) 0)).congr fun R' _ _ _ f => ?_
  have e : (h.map f).map (res O R') = 1 := by
    rw [← hh]; exact Matrix.ext fun a b => res_map f _
  simp only [FormData.HH, FormData.JR, mmul, map_alg, e, and_true, map_zero, Matrix.map_apply, Matrix.transpose_map]

private theorem HH_one : Φ.HH (1 : Matrix ι ι R) :=
  ⟨by simp, fun a b h => Matrix.one_apply_ne fun e => h (e ▸ rfl), mone _⟩

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}

private theorem hom_map {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (r : Lift O rbar R)
    (s : Γ) : (r.map f).hom s = (r.hom s).map f := rfl

private theorem hom_res (r : Lift O rbar R) (s : Γ) : (r.hom s).map (res O R) = rbar s := Matrix.ext (r.red s)

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

private theorem cut_InH (r0 : Lift O rbar O) (r : Lift O rbar R) :
    Cut O R fun R' _ _ _ f => Φ.InH r0.hom R' (r.map f) := by
  refine (Cut.all fun s => cut_HH Φ (r.hom s * (r0.hom s⁻¹).map (algebraMap O R)) ?_).congr fun R' _ _ _ f => ?_
  · have e : (r0.hom s⁻¹).map (algebraMap O (ResidueField O)) = rbar s⁻¹ := by
      rw [← hom_res r0]
      exact Matrix.ext fun a b => ((res O O).commutes _).symm
    rw [mmul, map_alg, hom_res, e, ← map_mul, mul_inv_cancel, map_one]
  · simp only [FormData.InH, mmul, map_alg, hom_map]

private theorem InH_self (r0 : Lift O rbar O) : Φ.InH r0.hom O r0 := fun s => by
  have e : (r0.hom s⁻¹).map (algebraMap O O) = r0.hom s⁻¹ := rfl
  rw [e, ← map_mul, mul_inv_cancel, map_one]
  exact HH_one Φ

end

section
variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {rbar : Γ →* Matrix ι ι (ResidueField O)}

private theorem all_univ {R0 : Type} [CommRing R0] [Algebra O R0] [IsCO O R0] (u : Lift O rbar R0)
    (hu : Represents (fun _ _ _ _ _ => True) u) (T : Type) [Finite T]
    (B : Type) [CommRing B] [Algebra O B] [IsCO O B] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (_ : IsCO O A) (i : B →ₐ[O] A) (r : Lift O rbar A)
      (α : T → Matrix ι ι A), (∀ v, (α v).map (res O A) = 1) ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (i' : B →ₐ[O] R') (r' : Lift O rbar R')
        (α' : T → Matrix ι ι R'), (∀ v, (α' v).map (res O R') = 1) →
        ∃! f : A →ₐ[O] R', f.comp i = i' ∧ r.map f = r' ∧ ∀ v, (α v).map f = α' v := by
  obtain ⟨S, _, _, _, j, i, hS⟩ := coprod2 (O := O) R0 B
  haveI := co_mvps O S (T × ι × ι)
  let Y : T → Matrix ι ι (MvPowerSeries (T × ι × ι) S) := fun v => Matrix.of fun a b => X (v, a, b)
  have hY : ∀ (R' : Type) [CommRing R'] [Algebra O R'] (f : MvPowerSeries (T × ι × ι) S →ₐ[O] R') v,
      (1 + Y v).map f = 1 + Matrix.of fun a b => f (X (v, a, b)) := fun R' _ _ f v => by
    rw [Matrix.map_add _ (map_add f), mone]; rfl
  refine ⟨MvPowerSeries (T × ι × ι) S, inferInstance, inferInstance, inferInstance, (Ca O _ S).comp i,
    u.map ((Ca O _ S).comp j), fun v => 1 + Y v, fun v => ?_, fun R' _ _ _ i' r' α' hα => ?_⟩
  · rw [hY, add_eq_left]
    exact Matrix.ext fun a b => (res_eq_zero_iff O _ _).2 (X_mem _)
  · obtain ⟨j', hj, hj'⟩ := (hu R').2 r' trivial
    obtain ⟨g, ⟨hg1, hg2⟩, hg⟩ := hS R' j' i'
    obtain ⟨f, ⟨h1, h2⟩, h3⟩ := co_ev O S R' (T × ι × ι) g (fun s => (α' s.1 - 1) s.2.1 s.2.2) fun s => by
      rw [← res_eq_zero_iff O]
      have : (α' s.1 - 1).map (res O R') = 0 := by rw [Matrix.map_sub _ (map_sub _), hα, mone, sub_self]
      exact congrFun (congrFun this s.2.1) s.2.2
    have h1' : f.comp (Ca O _ S) = g := AlgHom.ext h1
    refine ⟨f, ⟨?_, ?_, fun v => ?_⟩, fun f' ⟨k1, k2, k3⟩ => h3 f' ⟨fun x => ?_, fun s => ?_⟩⟩
    · rw [← AlgHom.comp_assoc, h1', hg2]
    · rw [← hj, ← hg1, ← h1']; rfl
    · rw [hY, ← eq_sub_iff_add_eq']
      exact Matrix.ext fun a b => h2 (v, a, b)
    · exact DFunLike.congr_fun (hg (f'.comp (Ca O _ S)) ⟨hj' _ k2, k1⟩) x
    · have := k3 s.1
      rw [hY, ← eq_sub_iff_add_eq'] at this
      exact congrFun (congrFun this s.2.1) s.2.2

private theorem framed_of_univ {X : Type} [AddCommGroup X] {w : ι → X} (Φ : FormData O w)
    {R0 : Type} [CommRing R0] [Algebra O R0] [IsCO O R0] (u : Lift O rbar R0)
    (hu : Represents (fun _ _ _ _ _ => True) u) (r0 : Lift O rbar O)
    (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q)))
    (hL : ∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) (hL0 : ∀ q, L q O (r0.comap (F.ψ q) (F.hψ q)))
    (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (i : B →ₐ[O] R) (r : Lift O rbar R)
      (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α := by
  haveI := (co_res O).1
  obtain ⟨A, _, _, _, i, r, α, hα, hA⟩ := all_univ u hu F.T B
  have c1 : Cut O A fun R' _ _ _ f => Φ.InH r0.hom R' (r.map f) ∧ (∀ v, Φ.HH ((α v).map f)) ∧ (α F.v0).map f = 1 ∧
      ∀ v s, (r.map f).hom (F.φ v s) * (α v).map f = (α v).map f * ((ρ v).hom s).map (f.comp i) := by
    refine ((cut_InH Φ r0 r).and ((Cut.all fun v => cut_HH Φ _ (hα v)).and ((Cut.mat (α F.v0) 1).and
      (Cut.all fun v => Cut.all fun s =>
        Cut.mat (r.hom (F.φ v s) * α v) (α v * ((ρ v).hom s).map i))))).congr fun R' _ _ _ f => ?_
    simp only [mone, mmul]
    rfl
  have e0 : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (r' : Lift O rbar R'),
      r'.map (res O R') = r0.map (res O O) := fun R' _ _ _ r' =>
    Lift.ext (MonoidHom.ext fun s => (hom_res r' s).trans (hom_res r0 s).symm)
  obtain ⟨A1, _, _, _, p, ⟨p1, p2, p3, p4⟩, hA1⟩ := c1.univ (res O A) (by
    refine ⟨?_, fun v => ?_, hα _, fun v s => ?_⟩
    · rw [e0]
      obtain ⟨I, hI⟩ := cut_InH Φ r0 r0
      refine (hI _ _).2 fun x hx => ?_
      rw [show x = 0 from (hI O (AlgHom.id O O)).1 (InH_self Φ r0) x hx, map_zero]
    · rw [hα]; exact HH_one Φ
    · rw [hα, mul_one, one_mul, hom_map, hom_res]
      exact Matrix.ext fun a b => ((res_map i _).trans ((ρ v).red s a b)).symm)
  have c2 : Cut O A1 fun R' _ _ _ f => ∀ q, L q R' (((r.map p).map f).comap (F.ψ q) (F.hψ q)) :=
    Cut.all fun q => (hL q).closed A1 ((r.map p).comap (F.ψ q) (F.hψ q)) fun s => by
      have := p1 (F.ψ q s)
      rwa [← map_inv] at this
  obtain ⟨A2, _, _, _, p', hp', hA2⟩ := c2.univ (res O A1) (fun q => by
    rw [e0]
    obtain ⟨I, hI⟩ := (hL q).closed O (r0.comap (F.ψ q) (F.hψ q)) (InH_self Φ (r0.comap (F.ψ q) (F.hψ q)))
    refine (hI _ (res O O)).2 fun x hx => ?_
    rw [show x = 0 from (hI O (AlgHom.id O O)).1 (hL0 q) x hx, map_zero])
  refine ⟨A2, inferInstance, inferInstance, inferInstance, (p'.comp p).comp i, r.map (p'.comp p),
    fun v => (α v).map (p'.comp p), ?_, fun R' _ _ _ i' r' α' ⟨k1, k2, k3, k4, k5⟩ => ?_⟩
  · obtain ⟨I, hI⟩ := c1
    obtain ⟨q1, q2, q3, q4⟩ := (hI A2 (p'.comp p)).2 fun x hx => by
      rw [AlgHom.comp_apply, (hI A1 p).1 ⟨p1, p2, p3, p4⟩ x hx, map_zero]
    exact ⟨q1, hp', q2, q3, q4⟩
  · obtain ⟨f, ⟨rfl, rfl, h3⟩, hf⟩ := hA R' i' r' α' fun v => (k3 v).2.2
    obtain rfl : α' = fun v => (α v).map f := funext fun v => (h3 v).symm
    obtain ⟨g, rfl, hg⟩ := hA1 R' f ⟨k1, k3, k4, k5⟩
    obtain ⟨g', rfl, hg'⟩ := hA2 R' g k2
    exact ⟨g', ⟨rfl, rfl, fun _ => rfl⟩, fun g'' h => hg' g'' (hg _ (hf ((g''.comp p').comp p) h))⟩

end

theorem UpperTheory.V.Alg.framed_univ :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ [Finite (ResidueField O)] [CharP (ResidueField O) l] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ], PhiCond Γ l → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (_ : Unit),
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (i : B →ₐ[O] R) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α := by
  intro l _ O _ _ _ _ ι X _ _ _ w Φ _ _ _ Γ _ _ _ rbar r0 _ _ _ _ _ hΦ F L _ hL hL0 B _ _ _ ρ _ _
  have hc : IsLocallyConstant rbar := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (r0.cont a b 1).eventually_eq x
    filter_upwards [this] with y hy
    refine Matrix.ext fun a b => ?_
    have h := Ideal.Quotient.eq.1 (hy a b)
    rw [pow_one, ← res_eq_zero_iff O, map_sub, sub_eq_zero, r0.red, r0.red] at h
    exact h
  obtain ⟨R0, _, _, _, u, hu⟩ := univ_lift l O Γ ι rbar hΦ hc
  exact framed_of_univ Φ u hu r0 F L hL hL0 B ρ
