import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RestrictionH1MemBlochKato

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.LocalSaturation

section Algebra

variable {O Λ X Y : Type} [CommRing O] [CommRing Λ] (ι : O →+* Λ) (F : Submodule O (X → Y → O))

def tensorSpan (B : Type) [AddCommGroup B] [Module Λ B] : Submodule Λ (X → Y → B) :=
  Submodule.span Λ {φ | ∃ c ∈ F, ∃ b : B, ∀ x y, φ x y = ι (c x y) • b}

variable [IsDomain O] [IsDiscreteValuationRing O]

theorem exists_dvd_all (c : X → Y → O) (hc : c ≠ 0) :
    ∃ x₀ y₀, c x₀ y₀ ≠ 0 ∧ ∀ x y, c x₀ y₀ ∣ c x y := by
  obtain ⟨x₁, hx₁⟩ := Function.ne_iff.1 hc
  obtain ⟨y₁, hy₁⟩ := Function.ne_iff.1 hx₁
  haveI : Nonempty (X × Y) := ⟨(x₁, y₁)⟩
  let p := Function.argmin fun p : X × Y => IsDiscreteValuationRing.addVal O (c p.1 p.2)
  have hp : ∀ x y, c p.1 p.2 ∣ c x y := fun x y =>
    IsDiscreteValuationRing.addVal_le_iff_dvd.1
      (Function.argmin_le (fun p : X × Y => IsDiscreteValuationRing.addVal O (c p.1 p.2)) (x, y))
  refine ⟨p.1, p.2, fun h => hy₁ ?_, hp⟩
  have := hp x₁ y₁
  rwa [h, zero_dvd_iff] at this

variable {B' B : Type} [AddCommGroup B'] [Module Λ B'] [AddCommGroup B] [Module Λ B]

theorem mem_tensorSpan_of_sum (hF : ∀ (a : O) (c : X → Y → O), a ≠ 0 → a • c ∈ F → c ∈ F)
    (f : B' →ₗ[Λ] B) (hf : Function.Injective f) (n : ℕ) :
    ∀ (c : Fin n → X → Y → O) (b : Fin n → B) (φ : X → Y → B'), (∀ j, c j ∈ F) →
      (∀ x y, f (φ x y) = ∑ j, ι (c j x y) • b j) → φ ∈ tensorSpan ι F B' := by
  induction n with
  | zero =>
    intro c b φ _ h
    have : φ = 0 := by
      funext x y
      apply hf
      simpa using h x y
    rw [this]
    exact Submodule.zero_mem _
  | succ n ih =>
    intro c b φ hc h
    by_cases h0 : c 0 = 0
    · refine ih (fun j => c j.succ) (fun j => b j.succ) φ (fun j => hc _) fun x y => ?_
      rw [h, Fin.sum_univ_succ, h0]
      simp
    · obtain ⟨x₀, y₀, hne, hdvd⟩ := exists_dvd_all (c 0) h0
      choose d hd using hdvd
      have hdF : d ∈ F := by
        refine hF _ d hne ?_
        have : c 0 x₀ y₀ • d = c 0 := by
          funext x y
          exact (hd x y).symm
        rw [this]
        exact hc 0
      have h1 : (fun x y => ι (d x y) • φ x₀ y₀) ∈ tensorSpan ι F B' :=
        Submodule.subset_span ⟨d, hdF, φ x₀ y₀, fun _ _ => rfl⟩
      have h2 : φ - (fun x y => ι (d x y) • φ x₀ y₀) ∈ tensorSpan ι F B' := by
        refine ih (fun j => c j.succ - c j.succ x₀ y₀ • d) (fun j => b j.succ) _
          (fun j => F.sub_mem (hc _) (F.smul_mem _ hdF)) fun x y => ?_
        simp only [Pi.sub_apply, Pi.smul_apply, map_sub, map_smul, h, Fin.sum_univ_succ, smul_eq_mul,
          map_mul, sub_smul, Finset.sum_sub_distrib, smul_add, Finset.smul_sum, smul_smul]
        rw [hd x y, map_mul, mul_comm (ι (d x y))]
        simp only [mul_comm (ι (d x y))]
        abel
      simpa using (tensorSpan ι F B').add_mem h2 h1

theorem mem_tensorSpan_of_map (hF : ∀ (a : O) (c : X → Y → O), a ≠ 0 → a • c ∈ F → c ∈ F)
    (f : B' →ₗ[Λ] B) (hf : Function.Injective f) (φ : X → Y → B')
    (h : (fun x y => f (φ x y)) ∈ tensorSpan ι F B) : φ ∈ tensorSpan ι F B' := by
  obtain ⟨n, a, g, hg⟩ := Submodule.mem_span_set'.1 h
  choose c hc b hb using fun j => (g j).2
  refine mem_tensorSpan_of_sum ι F hF f hf n c (fun j => a j • b j) φ hc fun x y => ?_
  have := congrFun (congrFun hg x) y
  simp only [Finset.sum_apply, Pi.smul_apply, hb] at this
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

end Algebra

section Bridge

open GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles GlobalTheory.BKIntegralToRational

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) (P : LocPrime l) {m : ℕ} (T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O)

def intCrys : Submodule O (↥Gw → Fin m → O) where
  carrier := {f | IsCrysCocycle Bw P T f}
  zero_mem' := by
    have := (Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))).zero_mem
    unfold IsCrysCocycle
    simpa [Pi.zero_def] using this
  add_mem' := fun {a b} ha hb => by
    have := (Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))).add_mem ha hb
    change IsCrysCocycle Bw P T _
    unfold IsCrysCocycle
    convert this using 1
    funext g j
    simp
  smul_mem' := fun a c hc => by
    have := (Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))).smul_mem (Bw.toLL a) hc
    change IsCrysCocycle Bw P T _
    unfold IsCrysCocycle
    convert this using 1
    funext g j
    simp

theorem intCrys_saturated (a : O) (c : ↥Gw → Fin m → O) (ha : a ≠ 0) (h : a • c ∈ intCrys Bw P T) :
    c ∈ intCrys Bw P T := by
  have ha' : Bw.toLL a ≠ 0 := (map_ne_zero_iff _ (toLL_injective Bw)).2 ha
  have := (Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))).smul_mem (Bw.toLL a)⁻¹ h
  change IsCrysCocycle Bw P T _
  unfold IsCrysCocycle
  convert this using 1
  funext g j
  simp [ha']

variable [IsTopologicalRing O]

omit [IsTopologicalRing O] in
theorem continuous_toLL : Continuous Bw.toLL :=
  continuous_subtype_val.comp Bw.eO_cont

theorem cob_mem_intCrys (hT : Continuous fun g => (T g : Matrix (Fin m) (Fin m) O)) (a : Fin m) :
    (fun (g : ↥Gw) j => ((T g : Matrix (Fin m) (Fin m) O) - 1) j a) ∈ intCrys Bw P T := by
  have hx : ∀ g j, Bw.toLL (((T (Bw.e.symm g : ↥Gw) : Matrix (Fin m) (Fin m) O) - 1) j a) =
      (Bw.rep (T.comp Gw.subtype) g (Pi.single a 1) - Pi.single a 1 : Fin m → ↥Bw.LL.1) j := by
    intro g j
    by_cases hj : j = a <;>
      simp [LocBridge.rep, Matrix.toLinAlgEquiv'_apply, Matrix.one_apply, Pi.single_apply, hj]
  change (fun (g : ↥(Loc.GK Bw.Kw)) (j : Fin m) =>
    Bw.toLL (((T (Bw.e.symm g : ↥Gw) : Matrix (Fin m) (Fin m) O) - 1) j a)) ∈
      Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))
  refine ⟨⟨?_, fun g h => ?_⟩, Pi.single a 1 ⊗ₜ 1, fun g => ?_⟩
  · refine continuous_pi fun j => (continuous_toLL Bw).comp ?_
    simp only [Matrix.sub_apply]
    exact (((continuous_apply_apply j a).comp hT).comp
      (continuous_subtype_val.comp Bw.e_symm_cont)).sub continuous_const
  · simp only [funext (hx _)]
    rw [map_mul, map_sub, Module.End.mul_apply]
    abel
  · simp only [funext (hx _)]
    simp [Formalism.WeaklyAdmissibleFiltrations.actVB, TensorProduct.sub_tmul]

variable {Λ : Type} [CommRing Λ] [Algebra O Λ] (κ : (Ω ≃ₐ[E] Ω) →* Λˣ)
  (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]

omit [TopologicalSpace O] [IsTopologicalRing O] [TopologicalSpace B] [DiscreteTopology B] in
theorem repOn_apply (hκ : ∀ g ∈ Gw, κ g = 1) (g : ↥Gw) (x : Fin m → B) (j : Fin m) :
    ((repOn T κ B).comp Gw.subtype) g x j =
      ∑ a, algebraMap O Λ ((T g : Matrix (Fin m) (Fin m) O) j a) • x a := by
  simp [repOn, matAct, hκ g g.2]

omit [TopologicalSpace B] [DiscreteTopology B] in
theorem cob_mem_tensorSpan (hT : Continuous fun g => (T g : Matrix (Fin m) (Fin m) O))
    (hκ : ∀ g ∈ Gw, κ g = 1) (x : Fin m → B) :
    (fun g => ((repOn T κ B).comp Gw.subtype) g x - x) ∈ tensorSpan (algebraMap O Λ) (intCrys Bw P T) B := by
  have : (fun g => ((repOn T κ B).comp Gw.subtype) g x - x) = ∑ a, fun (g : ↥Gw) j =>
      algebraMap O Λ (((T g : Matrix (Fin m) (Fin m) O) - 1) j a) • x a := by
    funext g j
    rw [Pi.sub_apply, repOn_apply T κ B hκ]
    simp only [Finset.sum_apply, Matrix.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]
    simp [Matrix.one_apply, apply_ite]
  rw [this]
  exact Submodule.sum_mem _ fun a _ =>
    Submodule.subset_span ⟨_, cob_mem_intCrys Bw P T hT a, x a, fun _ _ => rfl⟩

theorem smul_mem_Z1 [IsLocalRing O] (had : IsAdic (IsLocalRing.maximalIdeal O))
    [IsLocalRing Λ] [IsLocalHom (algebraMap O Λ)] (hB : Tors Λ B) (hκ : ∀ g ∈ Gw, κ g = 1)
    {c : ↥Gw → Fin m → O} (hc : c ∈ intCrys Bw P T) (b : B) :
    (fun g j => algebraMap O Λ (c g j) • b) ∈ Z1 ((repOn T κ B).comp Gw.subtype) := by
  refine ⟨continuous_pi fun j => ?_, fun g h => ?_⟩
  · have hcont : Continuous fun x : O => algebraMap O Λ x • b := by
      obtain ⟨n, hn⟩ := hB b
      refine IsLocallyConstant.continuous ?_
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      refine ⟨(fun y => y - x) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O),
        ((isAdic_iff.1 had).1 n).preimage (by fun_prop), by simp, fun y hy => ?_⟩
      rw [← sub_eq_zero, ← sub_smul, ← map_sub]
      refine hn _ ?_
      have h1 := Ideal.mem_map_of_mem (algebraMap O Λ) hy
      rw [Ideal.map_pow] at h1
      exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) n h1
    exact hcont.comp (continuous_of_crys Bw P hc j)
  · funext j
    rw [Pi.add_apply, repOn_apply T κ B hκ]
    beta_reduce
    rw [cocycle_of_crys Bw P hc g h j]
    simp [add_smul, Finset.sum_smul, mul_smul]

end Bridge

theorem continuous_Tgl {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    (i : X.Tw) (s : X.Sig i) :
    Continuous fun g => (Tgl i s g : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
  have h : Continuous fun g : GE N => (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) := by
    simp only [← map_inv]
    exact (X.twistCharacterFamily_continuous i _ _).comp continuous_inv
  simp only [Tgl_coe]
  exact h.smul (X.rhoS_cont i s)

theorem locSat (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ]
    [IsLocalHom (algebraMap (X.O0 i) Λ)] (κ : GE N →* Λˣ) (htriv : TrivAbove κ (X.l i)) : LocSat bkP i s κ := by
  intro v hv B' B _ _ _ _ _ _ _ _ hB f hf y hy
  have hκ : ∀ g ∈ DecV N v, κ g = 1 := htriv v hv _ (N.plOm.2 v)
  have hB' : Tors Λ B' := fun b => by
    obtain ⟨n, hn⟩ := hB (f b)
    exact ⟨n, fun x hx => hf (by rw [map_smul, hn x hx, map_zero])⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  unfold bkOn at hy ⊢
  rw [dif_pos hv] at hy ⊢
  have h1 : (fun g j => f (z.1 g j)) ∈ tensorSpan (algebraMap (X.O0 i) Λ)
      (intCrys (bkP.br i v hv) (D.loc (X.l i)) (Tgl i s)) B := by
    refine GlobalTheory.BlochKatoIntegralScalars.mem_of_mk_mem_span ((repOn (Tgl i s) κ B).comp (DecV N v).subtype) _
      (cob_mem_tensorSpan _ _ _ κ B (continuous_Tgl i s) hκ) _ ?_
      (cocycles1MapOfEquivariant _ _ (f.compLeft (Fin D.R.r)) continuous_of_discreteTopology
        (fun g m => repOn_map (Tgl i s) κ f g.1 m) z) hy
    rintro x ⟨w, c, y, b, hc, hcy, hw, rfl⟩
    refine ⟨w, Submodule.subset_span ⟨y, ?_, b, hw⟩, rfl⟩
    change GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles.IsCrysCocycle _ _ _ _
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles.IsCrysCocycle
    convert hc using 1
    funext g j
    rw [← hcy, MulEquiv.apply_symm_apply]
  have h2 := mem_tensorSpan_of_map _ _ (intCrys_saturated _ _ _) f hf z.1 h1
  have h3 : ∀ L : Submodule Λ (H1 ((repOn (Tgl i s) κ B').comp (DecV N v).subtype)),
      tensorSpan (algebraMap (X.O0 i) Λ) (intCrys (bkP.br i v hv) (D.loc (X.l i)) (Tgl i s)) B' ≤
        (L.comap (Submodule.mkQ _)).map (Z1 ((repOn (Tgl i s) κ B').comp (DecV N v).subtype)).subtype →
      Submodule.Quotient.mk z ∈ L := by
    intro L hL
    obtain ⟨u, hu, h⟩ := hL h2
    obtain rfl : u = z := Subtype.ext h
    exact hu
  refine h3 _ (Submodule.span_le.2 ?_)
  rintro φ ⟨c, hc, b, hφ⟩
  refine ⟨⟨_, smul_mem_Z1 _ _ _ κ B' (X.twistBaseCoefficientRing_isAdic i) hB' hκ hc b⟩, Submodule.subset_span
    ⟨_, _, c, b, hc, fun g a => ?_, fun _ _ => rfl, rfl⟩, ?_⟩
  · rw [MulEquiv.symm_apply_apply]
  · funext g j
    exact (hφ g j).symm

theorem main : LocalFiniteness → LocalTateDuality → LocalEulerChar → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → LocSat bkP i s κ := by
  intro _ _ _ _ D N X bkP i s Λ _ _ _ κ Q h
  haveI := h.2.1
  exact locSat D N X bkP i s Λ κ h.2.2.2.2.2.1

end GlobalTheory.LocalSaturation
