import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.EpsMulSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.TmulPMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FinrankWPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusEquivariantDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelPrimitiveDeRhamHodgeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRelativeFrobeniusPrimitiveDeRhamEqConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeFrobeniusGrpSchemeCharPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstDeRhamHomologyProjectiveOverTensorIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFirstDeRhamHomologyHodgeFiltrationOfField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundle

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord.LinPf

variable {k : Type} [Field k]

private theorem dual_annG {C P : Type*} [CommRing C] [AddCommGroup P] [Module k P]
    (ρ : C →+* Module.End k P) (a ε g : C)
    (h : ∀ x : Module.Dual k P, (ρ a).dualMap x = 0 → ∃ u, (ρ ε).dualMap x = (ρ g).dualMap u)
    (x : P) (hx : ρ g x = 0) : ∃ u v, x = ρ a u + ρ (1 - ε) v := by
  have hW : x ∈ LinearMap.range (ρ a) ⊔ LinearMap.range (ρ (1 - ε)) := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have h1 : (ρ a).dualMap φ = 0 :=
      LinearMap.ext fun y ↦ hφ _ (Submodule.mem_sup_left ⟨y, rfl⟩)
    have h2 : (ρ (1 - ε)).dualMap φ = 0 :=
      LinearMap.ext fun y ↦ hφ _ (Submodule.mem_sup_right ⟨y, rfl⟩)
    obtain ⟨u, hu⟩ := h φ h1
    have h3 : φ = (ρ ε).dualMap φ + (ρ (1 - ε)).dualMap φ := by
      refine LinearMap.ext fun y ↦ ?_
      have e : ρ ε y + ρ (1 - ε) y = y := by
        rw [map_sub, map_one]; simp
      rw [LinearMap.add_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply, ← map_add, e]
    rw [h3, h2, add_zero, hu, LinearMap.dualMap_apply, hx, map_zero]
  obtain ⟨y, ⟨u, rfl⟩, z, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 hW
  exact ⟨u, v, e.symm⟩

private theorem dual_annA {C P : Type*} [CommRing C] [AddCommGroup P] [Module k P]
    (ρ : C →+* Module.End k P) (a ε g : C) (hε : ρ ((1 - ε) * ε) = 0)
    (h : ∀ x : Module.Dual k P, (ρ g).dualMap x = 0 →
      ∃ u v, x = (ρ a).dualMap u + (ρ (1 - ε)).dualMap v)
    (x : P) (hx : ρ a x = 0) : ∃ u, ρ ε x = ρ g u := by
  have hW : ρ ε x ∈ LinearMap.range (ρ g) := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have h1 : (ρ g).dualMap φ = 0 := LinearMap.ext fun y ↦ hφ _ ⟨y, rfl⟩
    obtain ⟨u, v, rfl⟩ := h φ h1
    have e1 : ρ a (ρ ε x) = 0 := by
      have : ρ a * ρ ε = ρ ε * ρ a := by rw [← map_mul, ← map_mul, mul_comm]
      have := LinearMap.congr_fun this x
      simpa [hx] using this
    have e2 : ρ (1 - ε) (ρ ε x) = 0 := by
      have : ρ (1 - ε) * ρ ε = 0 := by rw [← map_mul, hε]
      exact LinearMap.congr_fun this x
    rw [LinearMap.add_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply, e1, e2, map_zero,
      map_zero, add_zero]
  obtain ⟨u, hu⟩ := hW
  exact ⟨u, hu.symm⟩

variable {p : ℕ} [Fact p.Prime]

private theorem frob_of_mem (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A)
    (c : primDR A) (hc : c ∈ PrimitiveSubmodule A) : frobDR p k hk A c = 0 := by
  letI : Algebra k k := (frobR p k hk).toAlgebra
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k A hA
  have hπ := isGrpPullback_pullback A (spMap (frobR p k hk))
  obtain ⟨F, hFm, hF⟩ := GlobalTheory.T.exists_relativeFrobenius_grpScheme_charP p k hk A _ _ hπ
  have hker := (GlobalTheory.T.range_relativeFrobenius_primitiveDeRham_eq_conjugate GlobalTheory.abelianDeRham.2.2.1 p k hk A _ _ hπ F hF g hA hg).2
  let m := GlobalTheory.Published.AbelianDeRham.bcMor hπ
  have e : primPull (dp0 k) (𝟙 _) F (m.pull c) = frobDR p k hk A c :=
    GrpMor.pull_pull m (homMor (dp0 k) (𝟙 _) F) (frobMor p k hk A (cast_left p k hk A))
      (fun _ ↦ rfl) hF c
  rw [← e]
  exact hker (m.isMor.pullback1_mem_hodgeFiltration hc)

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {t : Sp k ⟶ Sp R}

private theorem hom_apply (o : Obj b N t) (c : 𝓞 D.F) (h : HdR o.A) (x : primDR o.A) :
    hom o c h x = h (coh o c x) := rfl

private theorem sep (o : Obj b N t) {x y : primDR o.A} (e : ∀ h : HdR o.A, h x = h y) : x = y := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k]
  intro h
  have := e h
  rw [map_sub, sub_eq_zero]
  exact this

private theorem hom_add (o : Obj b N t) (x y : 𝓞 D.F) : hom o (x + y) = hom o x + hom o y := by
  simp only [hom, map_add]

private theorem hom_mul (o : Obj b N t) (x y : 𝓞 D.F) : hom o (x * y) = hom o x * hom o y := by
  simp only [hom, map_mul]

private theorem hom_one (o : Obj b N t) : hom o 1 = 1 := by
  simp only [hom, map_one]

private noncomputable def cohHom (o : Obj b N t) : 𝓞 D.F →+* Module.End k (primDR o.A) where
  toFun := coh o
  map_one' := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [← hom_apply, hom_one]; rfl
  map_mul' x y := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [mul_comm x y, ← hom_apply, hom_mul]; rfl
  map_zero' := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [← hom_apply]; simp [hom]
  map_add' x y := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [← hom_apply, hom_add, LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply, map_add]; rfl

private theorem cohHom_apply (o : Obj b N t) (c : 𝓞 D.F) : cohHom o c = coh o c := rfl

private theorem hom_eq (o : Obj b N t) (c : 𝓞 D.F) : hom o c = (cohHom o c).dualMap := rfl

private theorem cohHom_natCast_zero (hk : (p : k) = 0) (o : Obj b N t) : cohHom o (p : 𝓞 D.F) = 0 := by
  rw [map_natCast, ← map_natCast (algebraMap k (Module.End k (primDR o.A))) p, hk, map_zero]

end UpperTheory.Gal.Ord.LinPf

open UpperTheory.Gal.Ord.LinPf in
theorem UpperTheory.Gal.Ord.lin :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      Lin p π (β.comp (b.t i)) (coh o) (PrimitiveSubmodule o.A) (frobDR p k hk o.A).toAddMonoidHom := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i w f hw hn hf π
  obtain ⟨h1, ⟨h₀, h2, h3⟩, -⟩ := UpperTheory.Gal.Ord.lie p D R b N hN hNp hm k hk β o i w f hw hn hf π
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hk
  letI := tensorModule (dp0 k) (𝟙 _) (o.act.toF D)
  have hP := GlobalTheory.CrysProj.hdR_projective D.F k o.A o.ab (o.act.toF D)
  obtain ⟨hG, hA⟩ := UpperTheory.Gal.Ord.proj p k (𝓞 D.F) w f π (HdR o.A)
  have hs : ∀ (c : 𝓞 D.F) (x : HdR o.A), ((1 : k) ⊗ₜ[ℤ] c) • x = (cohHom o c).dualMap x := fun c x ↦ by
    change actAlg (dp0 k) (𝟙 _) (o.act.toF D) ((1 : k) ⊗ₜ[ℤ] c) x = _
    rw [actAlg_tmul, one_smul]
    rfl
  have hε : cohHom o ((1 - π.ε) * π.ε) = 0 := by
    obtain ⟨u, hu⟩ := π.idem
    have e : (1 - π.ε) * π.ε = (p : 𝓞 D.F) * (-u) := by
      linear_combination -hu
    rw [e, map_mul, cohHom_natCast_zero hk, zero_mul]
  refine
    { fin := ?_
      add := fun x y ↦ (cohHom o).map_add x y
      mul := fun x y ↦ (cohHom o).map_mul x y
      one := (cohHom o).map_one
      ker := hw
      semi := fun l x ↦ ?_
      comm := fun c x ↦ ?_
      kerΦ := fun x ↦ ⟨fun h ↦ GlobalTheory.T.frobenius_kernel_primitive_de_rham_hodge p k hk o.A o.ab x h, fun h ↦ frob_of_mem hk o.A o.ab x h⟩
      stab := fun c x hx ↦ ?_
      eig := fun c x hx ↦ ?_
      line := ?_
      annG := fun x hx ↦ ?_
      annA := fun x hx ↦ ?_
      dims := UpperTheory.Gal.Ord.dims p D R b N hN hNp hm k hk β o i w f hw hn hf π }
  · obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o.A o.ab
    have H := GlobalTheory.abelianDeRham
    obtain ⟨hfd, -, -⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o.A g o.ab hg
    exact Module.finite_dual_iff k |>.1 hfd
  · change frobDR p k hk o.A (l • x) = l ^ p • frobDR p k hk o.A x
    rw [LinearMap.map_smulₛₗ, frobR_apply]
  · haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    exact GlobalTheory.AbDatum.frobDR_primPull p hk _ x
  · haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    exact (homMor (dp0 k) (𝟙 _) (o.act.act (algebraMap (𝓞 D.F) D.O c))).isMor.pullback1_mem_hodgeFiltration hx
  · refine sep o fun h ↦ ?_
    have e := (Submodule.mem_dualAnnihilator _).1 (h1 c h) x hx
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hom_apply, hom_apply, hom_apply, smul_eq_mul,
      sub_eq_zero] at e
    have ec : coh o c (coh o π.ε x) = coh o π.ε (coh o c x) := by
      have := LinearMap.congr_fun ((cohHom o).map_mul c π.ε) x
      rw [mul_comm, (cohHom o).map_mul] at this
      exact this.symm
    rw [ec, map_smul, e]
    rfl
  · have hx₀ : ∃ x ∈ PrimitiveSubmodule o.A, hom o π.ε h₀ x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h2 ((Submodule.mem_dualAnnihilator _).2 hc)
    obtain ⟨x, hx, hne⟩ := hx₀
    rw [hom_apply] at hne
    refine ⟨x, hx, fun e ↦ hne (by rw [e, map_zero]), fun y hy ↦ ?_⟩
    refine ⟨h₀ (coh o π.ε y) / h₀ (coh o π.ε x), sep o fun h ↦ ?_⟩
    obtain ⟨m, hm⟩ := h3 h
    have ey := (Submodule.mem_dualAnnihilator _).1 hm y hy
    have ex := (Submodule.mem_dualAnnihilator _).1 hm x hx
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hom_apply, hom_apply, smul_eq_mul,
      sub_eq_zero] at ey ex
    rw [map_smul, ey, ex, smul_eq_mul]
    field_simp
  · refine dual_annG (cohHom o) π.a π.ε π.g (fun y hy ↦ ?_) x hx
    obtain ⟨u, hu⟩ := hA y (by rw [hs]; exact hy)
    exact ⟨u, by rw [← hs, ← hs]; exact hu⟩
  · refine dual_annA (cohHom o) π.a π.ε π.g hε (fun y hy ↦ ?_) x hx
    obtain ⟨u, v, huv⟩ := hG y (by rw [hs]; exact hy)
    exact ⟨u, v, by rw [← hs, ← hs]; exact huv⟩
