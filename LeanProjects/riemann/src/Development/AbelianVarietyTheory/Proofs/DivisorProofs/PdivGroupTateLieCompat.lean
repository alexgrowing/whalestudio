import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HodgeTateCokernel

theorem exists_retraction_range {p : ℕ} [Fact p.Prime] {M M' : Type} [CommGroup M] [CommGroup M']
    (f : M →* M') (hf : Function.Injective f) [Module.Finite ℤ_[p] (HTLat.Tate p M')] :
    ∃ r : HTLat.Tate p M' →ₗ[ℤ_[p]] LinearMap.range (HTLat.Tate.map p f),
      ∀ s : LinearMap.range (HTLat.Tate.map p f), r s = s := by
  set S := LinearMap.range (HTLat.Tate.map p f)
  have h1 : ∀ t, (p : ℤ_[p]) • t ∈ S → t ∈ S := by
    rintro t ⟨u, hu⟩
    have h : ∀ n, f (u.lev (n + 1)) = t.lev n := fun n => by
      rw [← HTLat.Tate.lev_map, hu, HTLat.Tate.lev_smul, PDiv.pow_digit_natCast (t.lev_pow _),
        t.lev_succ]
    exact ⟨HTLat.Tate.mk (fun n => u.lev (n + 1)) fun n =>
      ⟨hf (by rw [map_pow, h, t.lev_pow, map_one]), u.lev_succ _⟩, HTLat.Tate.ext h⟩
  have h2 : ∀ (n : ℕ) t, (p : ℤ_[p]) ^ n • t ∈ S → t ∈ S := fun n => by
    induction n with
    | zero => simp
    | succ n ih => exact fun t ht => h1 t (ih _ (by rwa [smul_smul, ← pow_succ]))
  haveI : Module.IsTorsionFree ℤ_[p] (HTLat.Tate p M' ⧸ S) := .of_smul_eq_zero fun a q h => by
    by_cases ha : a = 0
    · exact .inl ha
    obtain ⟨t, rfl⟩ := S.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      PadicInt.unitCoeff_spec ha, mul_smul] at h
    exact .inr ((Submodule.Quotient.mk_eq_zero _).2
      (h2 _ t ((S.smul_mem_iff' (PadicInt.unitCoeff ha)).1 h)))
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property S.mkQ LinearMap.id S.mkQ_surjective
  refine ⟨(LinearMap.id - σ ∘ₗ S.mkQ).codRestrict S fun t => ?_, fun s => Subtype.ext ?_⟩
  · change s.1 - σ (S.mkQ s.1) = s.1
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 s.2, map_zero, sub_zero]
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub]
    exact sub_eq_zero.2 (LinearMap.congr_fun hσ (S.mkQ t)).symm

theorem dual_ext {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] {q : O} (hq : q ≠ 0)
    {s : Set M} (hs : ∀ w : M, q • w ∈ Submodule.span O s) {y z : Module.Dual O M}
    (h : ∀ m ∈ s, y m = z m) : y = z := LinearMap.ext fun w => by
  have h1 : y (q • w) = z (q • w) := LinearMap.eqOn_span (s := s) h (hs w)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
  exact mul_left_cancel₀ hq h1

theorem cokernelBound_of_group : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∀ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) → (∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) → (∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x) → Module.Finite O G.omega → Module.Free O G.omega → (∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G)))) → CokernelBound P := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P G e l c ζ hζ hpair hdlog hfin hfree hspan f
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI : IsIntegrallyClosed O := P.integers.isIntegrallyClosed
  have hflip : Function.Bijective (pairT P.A P.eps).flip := by
    have h : (pairT P.A P.eps).flip = -pairT P.A P.eps :=
      LinearMap.ext₂ fun s t => ((isAlt_pairT P.A P.eps).neg_eq s t).symm
    rw [h]
    exact neg_bijective.comp P.pairT_bijective
  obtain ⟨r, hr⟩ : ∃ r : P.T →ₗ[ℤ_[p]] P.tateGt, ∀ s : P.tateGt, r s = s := by
    have h : Module.Finite ℤ_[p] P.T := inferInstance
    unfold Point.tateGt
    exact @exists_retraction_range p _ _ _ (_) (_) _ P.toA_injective h
  let u : ℤ_[p] ≃ₗ[ℤ_[p]] (PDivGroup.mu p O).Tate :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[p] _ ζ) hζ
  have hc : Function.Surjective c := fun χ => by
    obtain ⟨t, ht⟩ := hflip.2
      (u.symm.toLinearMap ∘ₗ (pairing G O).flip χ ∘ₗ e.symm.toLinearMap ∘ₗ r)
    refine ⟨t, (PDivGroup.tate_free_perfect p O C G).2.2.2.2.2.2.2.1 (LinearMap.ext fun s => ?_)⟩
    have h1 : pairT P.A P.eps (e s : P.T) t = u.symm (pairing G O (e.symm (r (e s : P.T))) χ) :=
      LinearMap.congr_fun ht (e s : P.T)
    rw [hr, LinearEquiv.symm_apply_apply] at h1
    change pairing G O s (c t) = pairing G O s χ
    rw [hpair, h1]
    exact u.apply_symm_apply _
  have hp : (p : O) ^ 2 ≠ 0 := pow_ne_zero _ fun h => by
    have h1 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h1
  have hext : ∀ {y z : G.Lie}, (∀ t, y (dlog (G := G) (c t)) = z (dlog (G := G) (c t))) → y = z :=
    fun h => dual_ext hp hspan (by
      rintro _ ⟨χ, rfl⟩
      obtain ⟨t, rfl⟩ := hc χ
      exact h t)
  have hadd : ∀ x y, l (lieAdd x y) = l x + l y := fun x y => hext fun t => by
    rw [LinearMap.add_apply, hdlog, hdlog, hdlog, omega_lieAdd]
  have hsc : ∀ (a : O) x, l (AvDefs.lieScale P.Gt a x) = a • l x := fun a x => hext fun t => by
    rw [LinearMap.smul_apply, hdlog, hdlog, omega_lieScale, smul_eq_mul]
  let F : Module.Dual O (Module.Dual O G.omega) :=
    { toFun := fun y => f.1 (l.symm y)
      map_add' := fun y z => by
        rw [← omega_lieAdd, l.symm_apply_eq.2 ((hadd (l.symm y) (l.symm z)).trans
          (by rw [l.apply_symm_apply, l.apply_symm_apply])).symm]
      map_smul' := fun a y => by
        rw [RingHom.id_apply, smul_eq_mul, ← omega_lieScale,
          l.symm_apply_eq.2 ((hsc a (l.symm y)).trans (by rw [l.apply_symm_apply])).symm] }
  obtain ⟨w, hw⟩ := (Module.bijective_dual_eval O G.omega).2 F
  have hfw : ∀ x, l x w = f.1 x := fun x => by
    have h1 : l x w = f.1 (l.symm (l x)) := LinearMap.congr_fun hw (l x)
    rwa [l.symm_apply_apply] at h1
  have key : ∀ m ∈ Submodule.span O (Set.range (dlog (G := G))),
      ∃ g ∈ LinearMap.range P.al, ∀ x, l x m = g.1 x := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨χ, rfl⟩ := hm
      obtain ⟨t, rfl⟩ := hc χ
      exact ⟨P.al₀ t, ⟨1 ⊗ₜ t, by rw [Point.al_tmul, one_smul]⟩, fun x => hdlog x t⟩
    | zero => exact ⟨0, zero_mem _, fun x => map_zero _⟩
    | add m n _ _ hm hn =>
      obtain ⟨g, hg, h⟩ := hm
      obtain ⟨g', hg', h'⟩ := hn
      exact ⟨g + g', add_mem hg hg', fun x => by rw [map_add, h, h']; rfl⟩
    | smul a m _ hm =>
      obtain ⟨g, hg, h⟩ := hm
      exact ⟨a • g, Submodule.smul_mem _ a hg, fun x => by rw [map_smul, h]; rfl⟩
  obtain ⟨g, hg, h⟩ := key _ (hspan w)
  have h2 : (p : O) ^ 2 • f = g := Subtype.ext (funext fun x => by
    rw [← h, map_smul, hfw]; rfl)
  rw [h2]
  exact hg

end GlobalTheory.HodgeTateCokernel
