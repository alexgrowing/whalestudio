import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.c_fm_exists_flags_dualflag

section Pure
variable {G M N : Type} [Field G] [AddCommGroup M] [Module G M] [AddCommGroup N] [Module G N] {r : ℕ}

theorem sum_colFrame (c : Fin r → M) (F : Matrix (Fin r) (Fin r) G) (g : Fin r → G) :
    ∑ b, g b • colFrame c F b = ∑ a, (F *ᵥ g) a • c a := by
  simp only [colFrame, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring_nf

theorem det_isUnit {c : Fin r → M} {F : Matrix (Fin r) (Fin r) G} (h : LinearIndependent G (colFrame c F)) :
    IsUnit F.det := by
  by_contra hd
  have h0 : F.det = 0 := by simpa [isUnit_iff_ne_zero] using hd
  obtain ⟨g, hg, hFg⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hg
  funext b
  have hs : ∑ b, g b • colFrame c F b = 0 := by
    rw [sum_colFrame, hFg]
    simp
  exact Fintype.linearIndependent_iff.mp h g hs b

theorem indep_colFrame {c : Fin r → M} (hc : LinearIndependent G c) {F : Matrix (Fin r) (Fin r) G}
    (h : IsUnit F.det) : LinearIndependent G (colFrame c F) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [sum_colFrame] at hg
  have h1 : F *ᵥ g = 0 := by
    funext a
    exact Fintype.linearIndependent_iff.mp hc _ hg a
  have h2 : g = F⁻¹ *ᵥ (F *ᵥ g) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
  intro i
  rw [h2, h1]
  simp

private theorem colFrame_colFrame_lemma {V : Type} [AddCommGroup V] [Module G V] (e : Fin r → V)
    (A B : Matrix (Fin r) (Fin r) G) : colFrame (colFrame e A) B = colFrame e (A * B) := by
  funext b
  simp only [colFrame, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring_nf

private theorem colFrame_inj_lemma_2 {c : Fin r → M} (hc : LinearIndependent G c)
    {A A' : Matrix (Fin r) (Fin r) G} (h : colFrame c A = colFrame c A') : A = A' := by
  ext a b
  have hb := congrFun h b
  have hs : ∑ k, (A k b - A' k b) • c k = 0 := by
    simp only [colFrame] at hb
    simp only [sub_smul, Finset.sum_sub_distrib, hb, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hc _ hs a)

theorem dual_change {c : Fin r → M} (hc : LinearIndependent G c) (w : Fin r → N)
    {F u B : Matrix (Fin r) (Fin r) G} (hF : IsUnit F.det) (hu : IsUnit u.det)
    (h : colFrame c u = colFrame (colFrame c F) B) :
    colFrame w Fᵀ⁻¹ = colFrame (colFrame w uᵀ⁻¹) Bᵀ := by
  rw [colFrame_colFrame_lemma] at h ⊢
  have huFB : u = F * B := colFrame_inj_lemma_2 hc (h.trans (colFrame_colFrame_lemma c F B).symm |>.trans (by rw [colFrame_colFrame_lemma]))
  have hB : IsUnit B.det := by
    rw [huFB, Matrix.det_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  congr 1
  rw [huFB, Matrix.transpose_mul, Matrix.mul_inv_rev, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose]), Matrix.mul_one]

private theorem coeff_lemma_3 {f : Fin r → M} (hf : LinearIndependent G f) (B : Matrix (Fin r) (Fin r) G)
    (d : Fin r → G) (k : Fin r) (h : ∑ l, B l k • f l = ∑ l, d l • f l) : ∀ l, B l k = d l := by
  intro l
  have hs : ∑ l, (B l k - d l) • f l = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hf _ hs l)

theorem step_le {c : Fin r → M} (hc : LinearIndependent G c) (w : Fin r → N)
    {F u : Matrix (Fin r) (Fin r) G} (hF : IsUnit F.det) (hu : IsUnit u.det)
    (h : ∀ i, flagStep G (colFrame c u) i = flagStep G (colFrame c F) i) (i : ℕ) :
    flagStep G (fun k => colFrame w Fᵀ⁻¹ k.rev) i ≤ flagStep G (fun k => colFrame w uᵀ⁻¹ k.rev) i := by
  set B := F⁻¹ * u with hBdef
  have huFB : u = F * B := by
    rw [hBdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF, Matrix.one_mul]
  have h' : colFrame c u = colFrame (colFrame c F) B := by
    rw [colFrame_colFrame_lemma, ← huFB]
  have hf : LinearIndependent G (colFrame c F) := indep_colFrame hc hF
  have htri : ∀ l k : Fin r, k < l → B l k = 0 := by
    intro l k hkl
    have hk : colFrame c u k ∈ flagStep G (colFrame c F) ((k : ℕ) + 1) := by
      rw [← h]
      exact Submodule.subset_span ⟨k, by simp, rfl⟩
    rw [flagStep, Finsupp.mem_span_image_iff_linearCombination] at hk
    obtain ⟨d, hd, hdx⟩ := hk
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hdx
    have hcoef := coeff_lemma_3 hf B (fun l => d l) k ((congrFun h' k).symm.trans hdx.symm)
    rw [hcoef l]
    rw [Finsupp.mem_supported'] at hd
    apply hd l
    simp only [Set.mem_setOf_eq, not_lt]
    exact hkl
  rw [dual_change hc w hF hu h']
  unfold flagStep
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hk, rfl⟩
  simp only [Set.mem_setOf_eq] at hk
  change ∑ a, Bᵀ a k.rev • colFrame w uᵀ⁻¹ a ∈ _
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases hak : k.rev ≤ a
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨a.rev, ?_, by simp⟩
    have := Fin.rev_le_iff.mp hak
    simp only [Set.mem_setOf_eq]
    exact lt_of_le_of_lt (Fin.le_def.mp this) hk
  · rw [Matrix.transpose_apply, htri _ _ (not_le.mp hak), zero_smul]
    exact Submodule.zero_mem _

theorem span_le {c : Fin r → M} (hc : LinearIndependent G c) (w : Fin r → N) (R : Subring G)
    {F u : Matrix (Fin r) (Fin r) G} (hF : IsUnit F.det) (hu : IsUnit u.det)
    (h : Submodule.span R (Set.range (colFrame c u)) = Submodule.span R (Set.range (colFrame c F))) :
    Submodule.span R (Set.range (colFrame w Fᵀ⁻¹)) ≤ Submodule.span R (Set.range (colFrame w uᵀ⁻¹)) := by
  set B := F⁻¹ * u with hBdef
  have huFB : u = F * B := by
    rw [hBdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF, Matrix.one_mul]
  have h' : colFrame c u = colFrame (colFrame c F) B := by
    rw [colFrame_colFrame_lemma, ← huFB]
  have hf : LinearIndependent G (colFrame c F) := indep_colFrame hc hF
  have hR : ∀ l k : Fin r, B l k ∈ R := by
    intro l k
    have hk : colFrame c u k ∈ Submodule.span R (Set.range (colFrame c F)) := by
      rw [← h]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [Submodule.mem_span_range_iff_exists_fun] at hk
    obtain ⟨d, hdx⟩ := hk
    have hcoef := coeff_lemma_3 hf B (fun l => (d l : G)) k ((congrFun h' k).symm.trans hdx.symm)
    rw [hcoef l]
    exact (d l).2
  rw [dual_change hc w hF hu h']
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  change ∑ a, Bᵀ a k • colFrame w uᵀ⁻¹ a ∈ _
  refine Submodule.sum_mem _ fun a _ => ?_
  exact Submodule.smul_mem (Submodule.span R (Set.range (colFrame w uᵀ⁻¹))) (⟨B k a, hR k a⟩ : R)
    (Submodule.subset_span ⟨a, rfl⟩)

theorem map_colFrame {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {i : Ω →+* G} {j : V →+ M}
    (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e) (v : Fin r → V) (P : Matrix (Fin r) (Fin r) Ω) :
    (fun k => j (colFrame v P k)) = colFrame (fun a => j (v a)) (P.map i) := by
  funext k
  simp [colFrame, hj]

end Pure

theorem isExtOver_mk (Ω G V : Type) [Field Ω] [Field G] [Algebra Ω G] [AddCommGroup V] [Module Ω V] :
    IsExtOver (algebraMap Ω G) (TensorProduct.mk Ω G V 1).toAddMonoidHom := by
  refine ⟨fun a e => ?_, fun n b hb => ?_⟩
  · show (1 : G) ⊗ₜ[Ω] (a • e) = algebraMap Ω G a • ((1 : G) ⊗ₜ[Ω] e)
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, mul_one,
      Algebra.algebraMap_eq_smul_one]
  · classical
    have hb' : LinearIndependent Ω b := hb
    have hs := hb'.linearIndepOn_id
    let Bs := Module.Basis.extend hs
    let f : Fin n → hs.extend (Set.range b).subset_univ := fun k => ⟨b k, hs.subset_extend _ ⟨k, rfl⟩⟩
    have hinj : Function.Injective f := fun x y hxy =>
      hb'.injective (by simpa only [f, Subtype.mk.injEq] using hxy)
    have hli := (Bs.baseChange G).linearIndependent.comp f hinj
    convert hli using 1
    all_goals try (funext k; simp only [Function.comp_apply, Module.Basis.baseChange_apply, Bs, f,
      Module.Basis.extend_apply_self])
    all_goals rfl

end PositivityTheory.Xgp.c_fm_exists_flags_dualflag

private theorem dual_lemma_4 {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ}
    (bO : Module.Basis (Fin r) Ω (Module.Dual Ω V)) (v : Fin r → V)
    (hv : ∀ a b, bO a (v b) = if a = b then 1 else 0) (P : Matrix (Fin r) (Fin r) Ω)
    (hPt : IsUnit Pᵀ.det) (a b : Fin r) :
    colFrame bO P a (colFrame v Pᵀ⁻¹ b) = if a = b then 1 else 0 := by
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv _ hPt) a) b
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  rw [← h1]
  show (∑ d, P d a • bO d) (∑ c, Pᵀ⁻¹ c b • v c) = _
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, map_sum, map_smul, hv, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

open PositivityTheory.Xgp.c_fm_exists_flags_dualflag in
theorem PositivityTheory.Xgp.t_c_fm_exists_flags_dualflag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (x : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S x) (τ : CMType H) (X' : Scheme.{0}) (G : Type) [Field G] [Algebra Ω G] (ξ' : Spec (CommRingCat.of G) ⟶ X') (pr : X' ⟶ 𝔐.X) (Li' : Type) [AddCommGroup Li'] [Module G Li'] (j : 𝔐.Li →+ Li') (bO : Module.Basis (Fin D.q) Ω (Module.Dual Ω (𝔐.Vgen (.inr τ)))) (v : Fin D.q → 𝔐.Vgen (.inr τ)) (u : Matrix (Fin D.q) (Fin D.q) G), IsExtOver (algebraMap Ω G) j → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ pr (algebraMap Ω G) → (∀ a b, bO a (v b) = if a = b then 1 else 0) → (∀ a, u a a = 1) → (∀ a b, a < b → u a b = 0) → ((omBundle 𝔐 τ).pull ξ' pr (TensorProduct.mk Ω G (Module.Dual Ω (𝔐.Vgen (.inr τ))) 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G (Module.Dual Ω (𝔐.Vgen (.inr τ))) 1 (bO l)) → ((𝔐.V (.inr τ)).pull ξ' pr j).IsFlagVBOn Set.univ (fun k => colFrame (fun a => j (v a)) uᵀ⁻¹ k.rev) := by
  intro E _ _ _ H D l Xo cc Y S Ω _ K _ J x 𝔐 τ X' G _ _ ξ' pr Li' _ _ j bO v u hj hdom hv hu1 hu0 hflag
  have hmk := isExtOver_mk Ω G (Module.Dual Ω (𝔐.Vgen (.inr τ)))
  set mk := (TensorProduct.mk Ω G (Module.Dual Ω (𝔐.Vgen (.inr τ))) 1).toAddMonoidHom with hmkdef
  have hc : LinearIndependent G (fun l => mk (bO l)) := hmk.2 _ bO bO.linearIndependent
  have hu : IsUnit u.det := by
    rw [Matrix.det_of_lowerTriangular u (fun _ _ hab => hu0 _ _ hab)]
    simp [hu1]
  have hw : LinearIndependent G (fun a => j (v a)) := by
    apply hj.2
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have h0 : ∑ b, g b • v b = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_sum] using hg
    have h2 := congrArg (bO a) h0
    simpa [map_sum, hv] using h2
  intro p _
  have hp : ∀ q' : Cpt ξ', genPt 𝔐.ξ ⤳ pr q'.1 := fun q' => by
    have h1 := q'.2.map pr.continuous
    rwa [RegAtDom.map_genPt hdom] at h1
  obtain ⟨U, hpU, b, hbflag, hbframe⟩ := hflag p trivial
  obtain ⟨U0, hU0, φ, -, hφframe⟩ := omBundle_isVB 𝔐 τ ⟨pr p.1, hp p⟩ trivial
  let Bg := bO.baseChange G
  let F : Matrix (Fin D.q) (Fin D.q) G := fun a k => Bg.repr (b k) a
  have hbF : b = colFrame (fun l => mk (bO l)) F := by
    funext k
    conv_lhs => rw [← Bg.sum_repr (b k)]
    simp only [colFrame, F, Bg, Module.Basis.baseChange_apply]
    rfl
  have hbind : LinearIndependent G b := (hbframe p trivial hpU).1
  have hF : IsUnit F.det := det_isUnit (hbF ▸ hbind)
  let P : Matrix (Fin D.q) (Fin D.q) Ω := fun a k => bO.repr (φ k) a
  have hφP : φ = colFrame bO P := by
    funext k
    exact (bO.sum_repr (φ k)).symm
  have hφind : LinearIndependent Ω φ := (hφframe _ trivial hU0).1
  have hP : IsUnit P.det := det_isUnit (hφP ▸ hφind)
  have hPt : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
  let Q := Pᵀ⁻¹
  let v' : Fin D.q → 𝔐.Vgen (.inr τ) := colFrame v Q
  have hdual : ∀ a b, φ a (v' b) = if a = b then 1 else 0 := by
    intro a b
    rw [hφP]
    exact dual_lemma_4 bO v hv P hPt a b
  let Pm := P.map (algebraMap Ω G)
  have hmkφ : (fun k => mk (φ k)) = colFrame (fun l => mk (bO l)) Pm := by
    rw [hφP]
    exact map_colFrame hmk.1 bO P
  have hQm : Q.map (algebraMap Ω G) = Pmᵀ⁻¹ := by
    symm
    apply Matrix.inv_eq_right_inv
    show (P.map (algebraMap Ω G))ᵀ * (Pᵀ⁻¹).map (algebraMap Ω G) = 1
    rw [← Matrix.transpose_map, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hPt,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hjv' : (fun k => j (v' k : 𝔐.Li)) = colFrame (fun a => j (v a)) Pmᵀ⁻¹ := by
    rw [← hQm]
    exact map_colFrame (j := j.comp (𝔐.Vgen (.inr τ)).subtype.toAddMonoidHom) (fun a e => hj.1 a e) v Q
  have hPm : IsUnit Pm.det := by
    have h1 : LinearIndependent G (fun k => mk (φ k)) := hmk.2 _ φ hφind
    rw [hmkφ] at h1
    exact det_isUnit h1
  refine ⟨U ⊓ pr ⁻¹ᵁ U0, ⟨hpU, hU0⟩, fun k => colFrame (fun a => j (v a)) Fᵀ⁻¹ k.rev, ?_, ?_⟩
  · have h1 : ∀ i, flagStep G (colFrame (fun l => mk (bO l)) u) i
        = flagStep G (colFrame (fun l => mk (bO l)) F) i := fun i => by
      rw [← hbF]
      exact (hbflag i).symm
    intro i
    exact le_antisymm (step_le hc _ hF hu h1 i) (step_le hc _ hu hF (fun i => (h1 i).symm) i)
  · rintro q' - ⟨hq'U, hq'U0⟩
    have hφq := hφframe ⟨pr q'.1, hp q'⟩ trivial hq'U0
    have hVq := (omBundle_dualFrame 𝔐 τ _ hφq).2 v' hdual
    have hpV := FlagPull.pull_isFrameAt hdom hj q' (hp q') hVq
    have hpO := FlagPull.pull_isFrameAt hdom hmk q' (hp q') hφq
    have hbq := hbframe q' trivial hq'U
    have hspan : Submodule.span (regAt ξ' q') (Set.range (colFrame (fun l => mk (bO l)) Pm))
        = Submodule.span (regAt ξ' q') (Set.range (colFrame (fun l => mk (bO l)) F)) := by
      rw [← hmkφ, ← hbF]
      exact hpO.2.symm.trans hbq.2
    refine ⟨?_, ?_⟩
    · have hind := indep_colFrame hw (F := Fᵀ⁻¹)
        (Matrix.isUnit_nonsing_inv_det _ (by rwa [Matrix.det_transpose]))
      exact hind.comp Fin.rev Fin.rev_injective
    · rw [hpV.2, hjv']
      have hr : Set.range (fun (k : Fin D.q) => colFrame (fun a => j (v a)) Fᵀ⁻¹ k.rev)
          = Set.range (colFrame (fun a => j (v a)) Fᵀ⁻¹) := Fin.rev_surjective.range_comp (colFrame (fun a => j (v a)) Fᵀ⁻¹)
      rw [hr]
      exact le_antisymm (span_le hc _ _ hPm hF hspan.symm) (span_le hc _ _ hF hPm hspan)
