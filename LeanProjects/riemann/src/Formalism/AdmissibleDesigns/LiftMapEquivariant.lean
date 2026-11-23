import Formalism.AdmissibleDesigns.FinDimOfLat
import Formalism.AdmissibleDesigns.LenComapSurj

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Formalism.NG Module Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.FIN

section SpanK

variable {O : Type} [CommRing O] [IsDomain O] {H : Type} [AddCommGroup H] [Module O H]
  [Module (FractionRing O) H] [IsScalarTower O (FractionRing O) H]

theorem mem_spanK (S : Submodule O H) {x : H} (hx : x ∈ Submodule.span (FractionRing O) (S : Set H)) :
    ∃ t : O, t ≠ 0 ∧ t • x ∈ S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact S.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    rw [smul_add, mul_smul, mul_comm s t, mul_smul]
    exact S.add_mem (S.smul_mem s hty) (S.smul_mem t hsz)
  | smul a y _ hy =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) a
    dsimp only at hnd
    have key : (d : O) • a = algebraMap O (FractionRing O) n := by
      rw [← hnd, Algebra.smul_def, mul_comm]
      exact IsLocalization.mk'_spec (FractionRing O) n d
    refine ⟨(d : O) * t, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) ht, ?_⟩
    have e : ((d : O) * t) • (a • y) = n • (t • y) := by
      rw [mul_comm, ← smul_smul, ← smul_assoc (d : O) a y, key, algebraMap_smul, smul_comm]
    rw [e]
    exact S.smul_mem n hty

end SpanK

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {LL : Type} [Field LL] [TopologicalSpace LL] (e : FractionRing O ≃+* LL) {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] (eO : O ≃+* Ow)
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {Γ G : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {VT VT' : Type}
  [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  (Dt : LatData O Γ VT VT')

def psiR : (Γ → Dt.T') →ₛₗ[(eO : O →+* Ow)] (G → TrV e VT') where
  toFun c g := tr e ((c (ι g) : VT'))
  map_add' a b := by
    funext g
    rfl
  map_smul' a c := by
    funext g
    show tr e (a • ((c (ι g) : VT'))) = eO a • tr e ((c (ι g) : VT'))
    rw [smul_eO heO]

theorem psiR_apply (c : Γ → Dt.T') (g : G) : psiR e eO heO ι Dt c g = tr e ((c (ι g) : VT')) := rfl

theorem psiR_inj (hι : Function.Bijective ι) : Function.Injective (psiR e eO heO ι Dt) := by
  intro a b h
  funext γ
  obtain ⟨g, rfl⟩ := hι.2 γ
  exact Subtype.ext (congrFun h g)

variable [Module (FractionRing O) (ReciprocityTheory.Gal.H1 Dt.ρT')] [IsScalarTower O (FractionRing O) (ReciprocityTheory.Gal.H1 Dt.ρT')]

def FsG : Submodule O (ReciprocityTheory.Gal.H1 Dt.ρTl') :=
  ((Submodule.span (FractionRing O) (finiteClassesContinuous e PD ι Dt.ρT' Dt.ρT' LinearMap.id :
    Set (ReciprocityTheory.Gal.H1 Dt.ρT'))).restrictScalars O).comap Dt.j'

theorem coe_rhoTl' (γ : Γ) (t : Dt.T') : ((Dt.ρTl' γ t : Dt.T') : VT') = Dt.ρT' γ t := rfl

theorem mem_FsG (hcob : ∀ v : VT', (fun γ => Dt.ρT' γ v - v) ∈ finZ e PD Dt.ρT' ι)
    (x : ReciprocityTheory.Gal.Z1 Dt.ρTl') :
    Submodule.mkQ _ x ∈ FsG e PD ι Dt ↔ (fun γ => ((x : Γ → Dt.T') γ : VT')) ∈ finZ e PD Dt.ρT' ι := by
  have hx' : (fun γ => ((x : Γ → Dt.T') γ : VT')) ∈ ReciprocityTheory.Gal.Z1 Dt.ρT' :=
    ⟨continuous_subtype_val.comp x.2.1, fun g h => by
      show (((x : Γ → Dt.T') (g * h) : Dt.T') : VT') = _
      rw [x.2.2 g h]
      rfl⟩
  have hj : Dt.j' (Submodule.mkQ _ x) = Submodule.mkQ _ ⟨_, hx'⟩ := rfl
  constructor
  · intro hF
    have hF' : Dt.j' (Submodule.mkQ _ x) ∈ Submodule.span (FractionRing O) (finiteClassesContinuous e PD ι Dt.ρT' Dt.ρT' LinearMap.id :
        Set (ReciprocityTheory.Gal.H1 Dt.ρT')) := hF
    obtain ⟨t, ht, hS⟩ := mem_spanK _ hF'
    rw [hj, ← map_smul] at hS
    obtain ⟨f, hf, hfe⟩ := hS
    have hfz : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') ∈ finZ e PD Dt.ρT' ι := hf
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hfe
    obtain ⟨v, hv⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 hfe
    have htK : algebraMap O (FractionRing O) t ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht)
    have heq : (fun γ => ((x : Γ → Dt.T') γ : VT')) =
        (algebraMap O (FractionRing O) t)⁻¹ • (((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') -
          fun γ => Dt.ρT' γ v - v) := by
      funext γ
      have e1 : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ - t • ((x : Γ → Dt.T') γ : VT') = Dt.ρT' γ v - v :=
        hv γ
      show ((x : Γ → Dt.T') γ : VT') = (algebraMap O (FractionRing O) t)⁻¹ •
        (((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ - (Dt.ρT' γ v - v))
      have e2 : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ - (Dt.ρT' γ v - v) =
          algebraMap O (FractionRing O) t • ((x : Γ → Dt.T') γ : VT') := by
        rw [algebraMap_smul]
        have e3 : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ = Dt.ρT' γ v - v + t • ((x : Γ → Dt.T') γ : VT') := by
          rw [← e1]
          abel
        rw [e3]
        abel
      rw [e2, smul_smul, inv_mul_cancel₀ htK, one_smul]
    rw [heq]
    exact (finZ e PD Dt.ρT' ι).smul_mem _ ((finZ e PD Dt.ρT' ι).sub_mem hfz (hcob v))
  · intro h
    show Dt.j' (Submodule.mkQ _ x) ∈ Submodule.span (FractionRing O) _
    rw [hj]
    exact Submodule.subset_span ⟨⟨_, hx'⟩, h, rfl⟩

variable {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
  [ContinuousConstSMul O T₁] [AddCommGroup T₂] [Module O T₂] [Module.Finite O T₁] [Module.Free O T₁]
  [Module.Finite O Dt.T'] [Module.Free O Dt.T']
  (ρ₁ : Representation O Γ T₁) (π : T₁ →ₗ[O] T₂) (v : T₂ ≃ₗ[O] Dt.T')
  (hc : Continuous fun t => v (π t)) (he : ∀ g t, v (π (ρ₁ g t)) = Dt.ρTl' g (v (π t)))
  (hsp : ∀ x : VT', ∃ c : O, c ≠ 0 ∧ ∃ m : Dt.T', Dt.T'.subtype m = c • x)

def imG : Submodule O (ReciprocityTheory.Gal.H1 Dt.ρTl') :=
  (finiteClassesContinuousLattice e PD ι ρ₁).map (gRow Dt ρ₁ π v hc he)

abbrev L1 : Lattice (O := Ow) (repL e (locRep ρ₁) ι) :=
  latOf e eO (mkK (O := O) (M := T₁)) ι heO (locRep ρ₁) ρ₁ mkK_inj (fun γ m => (locRep_mkK ρ₁ γ m).symm) mkK_span

abbrev L2 : Lattice (O := Ow) (repL e Dt.ρT' ι) :=
  latOf e eO Dt.T'.subtype ι heO Dt.ρT' Dt.ρTl' Subtype.val_injective (fun _ _ => rfl) hsp

abbrev f0 : MK (O := O) T₁ →ₗ[O] VT' := liftK (Dt.T'.subtype ∘ₗ v.toLinearMap ∘ₗ π)

theorem lift_map_mk (m : T₁) : f0 Dt π v (mkK m) = Dt.T'.subtype ((v.toLinearMap ∘ₗ π) m) := liftK_mkK _ m

include he in
theorem lift_map_equivariant (γ : Γ) (x : MK (O := O) T₁) : f0 Dt π v (locRep ρ₁ γ x) = Dt.ρT' γ (f0 Dt π v x) :=
  liftK_equiv Dt.ρT' ρ₁ _ (fun g m => congrArg Subtype.val (he g m)) γ x

abbrev FR : LatHom (L1 e eO heO ι ρ₁) (L2 e eO heO ι Dt hsp) :=
  latHom ι heO mkK_inj Subtype.val_injective (fun γ m => (locRep_mkK ρ₁ γ m).symm) (fun _ _ => rfl) mkK_span hsp
    (lift_map_equivariant Dt ρ₁ π v he) (fun m => lift_map_mk Dt π v m)

theorem psi_mem_Z1fT (hcob : ∀ x : VT', (fun γ => Dt.ρT' γ x - x) ∈ finZ e PD Dt.ρT' ι)
    (x : ReciprocityTheory.Gal.Z1 Dt.ρTl') (hx : Submodule.mkQ _ x ∈ FsG e PD ι Dt) :
    psiR e eO heO ι Dt (x : Γ → Dt.T') ∈ latticeFiniteCocycles PD (L2 e eO heO ι Dt hsp) := by
  have h : psiR e eO heO ι Dt (x : Γ → Dt.T') ∈ finiteCocycles PD (repL e Dt.ρT' ι) := (mem_FsG e PD ι Dt hcob x).1 hx
  exact ⟨⟨h.1, fun g _ => ⟨(x : Γ → Dt.T') (ι g), rfl⟩⟩, h⟩

theorem exists_pre (hι : Function.Bijective ι)
    (hcob : ∀ x : VT', (fun γ => Dt.ρT' γ x - x) ∈ finZ e PD Dt.ρT' ι)
    (htopV : ∀ c : Γ → VT', Continuous (fun g => tr e (c (ι g))) → Continuous c)
    (y : G → TrV e VT') (hy : y ∈ latticeFiniteCocycles PD (L2 e eO heO ι Dt hsp)) :
    ∃ x : ReciprocityTheory.Gal.Z1 Dt.ρTl', Submodule.mkQ _ x ∈ FsG e PD ι Dt ∧ psiR e eO heO ι Dt (x : Γ → Dt.T') = y := by
  let σ : Γ ≃ G := (Equiv.ofBijective ι hι).symm
  have hισ : ∀ γ, ι (σ γ) = γ := fun γ => (Equiv.ofBijective ι hι).apply_symm_apply γ
  have hσι : ∀ g, σ (ι g) = g := fun g => (Equiv.ofBijective ι hι).symm_apply_apply g
  have hσmul : ∀ γ δ, σ (γ * δ) = σ γ * σ δ := fun γ δ => hι.1 (by rw [hισ, ι.map_mul, hισ, hισ])
  have hval : ∀ g, ∃ m : Dt.T', tr e (Dt.T'.subtype m) = y g := fun g => hy.1.2 g (Set.mem_univ g)
  let x0 : Γ → Dt.T' := fun γ => Classical.choose (hval (σ γ))
  have hx0 : ∀ γ, ((x0 γ : Dt.T') : VT') = untr e (y (σ γ)) := fun γ => Classical.choose_spec (hval (σ γ))
  have hpsi : psiR e eO heO ι Dt x0 = y := by
    funext g
    show ((x0 (ι g) : Dt.T') : VT') = untr e (y g)
    rw [hx0, hσι]
  have hcv : Continuous fun γ => ((x0 γ : Dt.T') : VT') := by
    apply htopV
    have : (fun g => tr e (((x0 (ι g) : Dt.T') : VT'))) = y := hpsi
    rw [this]
    exact hy.1.1.1
  have hcont : Continuous x0 := continuous_induced_rng.2 hcv
  have hcoc : ∀ γ δ, x0 (γ * δ) = x0 γ + Dt.ρTl' γ (x0 δ) := by
    intro γ δ
    apply Subtype.ext
    show ((x0 (γ * δ) : Dt.T') : VT') = ((x0 γ : Dt.T') : VT') + Dt.ρT' γ ((x0 δ : Dt.T') : VT')
    rw [hx0, hx0, hx0, hσmul]
    have h2 := hy.1.1.2 (σ γ) (σ δ)
    show untr e (y (σ γ * σ δ)) = untr e (y (σ γ)) + Dt.ρT' γ (untr e (y (σ δ)))
    rw [h2]
    show untr e (y (σ γ)) + Dt.ρT' (ι (σ γ)) (untr e (y (σ δ))) = _
    rw [hισ]
  let x : ReciprocityTheory.Gal.Z1 Dt.ρTl' := ⟨x0, hcont, hcoc⟩
  refine ⟨x, (mem_FsG e PD ι Dt hcob x).2 ?_, hpsi⟩
  show psiR e eO heO ι Dt x0 ∈ finiteCocycles PD (repL e Dt.ρT' ι)
  rw [hpsi]
  exact hy.2

theorem im_iff (hι : Function.Bijective ι)
    (htop1 : ∀ c : Γ → T₁, Continuous (fun g => tr e (mkK (O := O) (c (ι g)))) → Continuous c)
    (x : ReciprocityTheory.Gal.Z1 Dt.ρTl') :
    Submodule.mkQ _ x ∈ imG e PD ι Dt ρ₁ π v hc he ↔
      psiR e eO heO ι Dt (x : Γ → Dt.T') ∈ (FR e eO heO ι Dt ρ₁ π v he hsp).ImF PD := by
  let σ : Γ ≃ G := (Equiv.ofBijective ι hι).symm
  have hισ : ∀ γ, ι (σ γ) = γ := fun γ => (Equiv.ofBijective ι hι).apply_symm_apply γ
  have hσι : ∀ g, σ (ι g) = g := fun g => (Equiv.ofBijective ι hι).symm_apply_apply g
  have hσmul : ∀ γ δ, σ (γ * δ) = σ γ * σ δ := fun γ δ => hι.1 (by rw [hισ, ι.map_mul, hισ, hισ])
  constructor
  · rintro ⟨z, ⟨c₁, hc₁, rfl⟩, hzx⟩
    have hfin : (fun γ => mkK (O := O) ((c₁ : Γ → T₁) γ)) ∈ finZ e PD (locRep ρ₁) ι := hc₁
    have hzx' : Submodule.mkQ _ (ReciprocityTheory.Gal.cocycles1MapOfEquivariant ρ₁ Dt.ρTl' (v.toLinearMap ∘ₗ π) hc he c₁) =
        Submodule.mkQ _ x := hzx
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hzx'
    obtain ⟨t, ht⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 hzx'
    let d₁ : G → TrV e (MK (O := O) T₁) := fun g => tr e (mkK (O := O) ((c₁ : Γ → T₁) (ι g)))
    have hd₁ : d₁ ∈ latticeFiniteCocycles PD (L1 e eO heO ι ρ₁) := ⟨⟨hfin.1, fun g _ => ⟨_, rfl⟩⟩, hfin⟩
    refine Submodule.mem_sup.2 ⟨_, ⟨d₁, hd₁, rfl⟩, _, ⟨tr e (((-t : Dt.T')) : VT'), ⟨-t, rfl⟩, rfl⟩, ?_⟩
    funext g
    have h1 : ((v (π ((c₁ : Γ → T₁) (ι g))) : Dt.T') : VT') - (((x : Γ → Dt.T') (ι g) : Dt.T') : VT') =
        Dt.ρT' (ι g) (t : VT') - (t : VT') := congrArg Subtype.val (ht (ι g))
    show f0 Dt π v (mkK ((c₁ : Γ → T₁) (ι g))) + (Dt.ρT' (ι g) (((-t : Dt.T')) : VT') - (((-t : Dt.T')) : VT')) =
      (((x : Γ → Dt.T') (ι g) : Dt.T') : VT')
    rw [lift_map_mk]
    have h2 : (((x : Γ → Dt.T') (ι g) : Dt.T') : VT') =
        ((v (π ((c₁ : Γ → T₁) (ι g))) : Dt.T') : VT') - (Dt.ρT' (ι g) (t : VT') - (t : VT')) := by
      rw [← h1]
      abel
    rw [h2]
    simp only [Submodule.coe_neg, map_neg]
    show ((v (π ((c₁ : Γ → T₁) (ι g))) : Dt.T') : VT') + (-(Dt.ρT' (ι g) (t : VT')) - -(t : VT')) = _
    abel
  · intro h
    obtain ⟨a, ⟨d₁, hd₁, rfl⟩, b, ⟨yv, ⟨t, rfl⟩, rfl⟩, hab⟩ := Submodule.mem_sup.1 h
    have hval : ∀ g, ∃ m : T₁, tr e (mkK (O := O) m) = d₁ g := fun g => hd₁.1.2 g (Set.mem_univ g)
    let c0 : Γ → T₁ := fun γ => Classical.choose (hval (σ γ))
    have hc0 : ∀ γ, mkK (O := O) (c0 γ) = untr e (d₁ (σ γ)) := fun γ => Classical.choose_spec (hval (σ γ))
    have hd : (fun g => tr e (mkK (O := O) (c0 (ι g)))) = d₁ := by
      funext g
      show mkK (O := O) (c0 (ι g)) = untr e (d₁ g)
      rw [hc0, hσι]
    have hcont : Continuous c0 := htop1 c0 (by rw [hd]; exact hd₁.1.1.1)
    have hcoc : ∀ γ δ, c0 (γ * δ) = c0 γ + ρ₁ γ (c0 δ) := by
      intro γ δ
      apply mkK_inj (O := O)
      rw [map_add, ← locRep_mkK, hc0, hc0, hc0, hσmul]
      have h2 := hd₁.1.1.2 (σ γ) (σ δ)
      show untr e (d₁ (σ γ * σ δ)) = untr e (d₁ (σ γ)) + locRep ρ₁ γ (untr e (d₁ (σ δ)))
      rw [h2]
      show untr e (d₁ (σ γ)) + locRep ρ₁ (ι (σ γ)) (untr e (d₁ (σ δ))) = _
      rw [hισ]
    let c₁ : ReciprocityTheory.Gal.Z1 ρ₁ := ⟨c0, hcont, hcoc⟩
    have hfin : (fun γ => mkK (O := O) (c0 γ)) ∈ finZ e PD (locRep ρ₁) ι := by
      show (fun g => tr e (mkK (O := O) (c0 (ι g)))) ∈ finiteCocycles PD (repL e (locRep ρ₁) ι)
      rw [hd]
      exact hd₁.2
    refine ⟨Submodule.mkQ _ c₁, ⟨c₁, hfin, rfl⟩, ?_⟩
    show Submodule.mkQ _ (ReciprocityTheory.Gal.cocycles1MapOfEquivariant ρ₁ Dt.ρTl' (v.toLinearMap ∘ₗ π) hc he c₁) = Submodule.mkQ _ x
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine (ReciprocityTheory.Gal.mem_coboundaries1 _ _).2 ⟨-t, fun γ => ?_⟩
    apply Subtype.ext
    have h3 := congrFun hab (σ γ)
    have h5 : f0 Dt π v (untr e (d₁ (σ γ))) + (Dt.ρT' (ι (σ γ)) (t : VT') - (t : VT')) =
        (((x : Γ → Dt.T') (ι (σ γ)) : Dt.T') : VT') := h3
    rw [← hc0, lift_map_mk, hισ] at h5
    have h4 : ((v (π (c0 γ)) : Dt.T') : VT') + (Dt.ρT' γ (t : VT') - (t : VT')) =
        (((x : Γ → Dt.T') γ : Dt.T') : VT') := h5
    show ((v (π (c0 γ)) : Dt.T') : VT') - (((x : Γ → Dt.T') γ : Dt.T') : VT') =
      Dt.ρT' γ ((-t : Dt.T') : VT') - ((-t : Dt.T') : VT')
    rw [← h4]
    simp only [Submodule.coe_neg, map_neg]
    abel

theorem len_eq_col (hι : Function.Bijective ι)
    (hcob : ∀ x : VT', (fun γ => Dt.ρT' γ x - x) ∈ finZ e PD Dt.ρT' ι)
    (htopV : ∀ c : Γ → VT', Continuous (fun g => tr e (c (ι g))) → Continuous c)
    (htop1 : ∀ c : Γ → T₁, Continuous (fun g => tr e (mkK (O := O) (c (ι g)))) → Continuous c) :
    Module.length O (↥(FsG e PD ι Dt) ⧸ (imG e PD ι Dt ρ₁ π v hc he).comap (FsG e PD ι Dt).subtype) =
      (FR e eO heO ι Dt ρ₁ π v he hsp).col PD := by
  haveI h1 := RingHomInvPair.of_ringEquiv eO
  haveI h2 := RingHomInvPair.symm (eO : O →+* Ow) (eO.symm : Ow →+* O)
  rw [← len_comap_surj (Submodule.mkQ _) (Submodule.mkQ_surjective _)]
  unfold LatHom.col
  refine len_semi eO ((psiR e eO heO ι Dt).comp (ReciprocityTheory.Gal.Z1 Dt.ρTl').subtype)
    ((psiR_inj e eO heO ι Dt hι).comp Subtype.val_injective) _ _ _ _ ?_ ?_
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := exists_pre e eO heO PD ι Dt hsp hι hcob htopV y hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact psi_mem_Z1fT e eO heO PD ι Dt hsp hcob x hx
  · intro x _
    exact im_iff e eO heO PD ι Dt ρ₁ π v hc he hsp hι htop1 x

end Gen

end Formalism.MainNotions.N.KRow

end
