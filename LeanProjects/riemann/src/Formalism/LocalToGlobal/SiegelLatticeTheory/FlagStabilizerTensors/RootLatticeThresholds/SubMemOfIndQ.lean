import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCounting

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Flag

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem fix_e {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) (i : Fin D.R.rS) :
    c (F0.e i) = F0.e i := by
  have h := hfix (Fin.castSucc i)
  simpa [FlagG.fvec] using h

theorem fix_X {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) :
    ∀ x ∈ F0.X, c x = x := by
  intro x hx
  have h := LinearMap.eqOn_span' (f := (c : (VS D).V →ₗ[D.host.E] (VS D).V)) (g := LinearMap.id)
    (s := Set.range F0.e) (fun y ⟨i, hi⟩ => by rw [← hi]; exact fix_e F0 hfix i) hx
  simpa using h

theorem inv_fix {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) :
    ∀ a, c⁻¹ (F0.fvec a) = F0.fvec a := by
  intro a
  show c.symm (F0.fvec a) = F0.fvec a
  rw [LinearEquiv.symm_apply_eq, hfix]

theorem Xa_le_X (j : ℕ) : F0.Xa j ≤ F0.X := Submodule.span_mono (Set.image_subset_range _ _)

theorem perp_maps {c : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) : ∀ y ∈ perpS (VS D) F0.X, c y ∈ perpS (VS D) F0.X := by
  intro y hy x hx
  have h1 : c x = x := fix_X F0 hfix x hx
  have h2 := hc x y
  rw [h1] at h2
  rw [h2]
  exact hy x hx

def indQ (c : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) : WbQ D F0 → WbQ D F0 :=
  Submodule.mapQ _ _ ((c : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (perp_maps F0 hc hfix)) (by
    intro y hy
    simp only [Submodule.mem_comap, Submodule.coe_subtype] at hy ⊢
    rw [LinearMap.restrict_coe_apply]
    show c (y : (VS D).V) ∈ F0.X
    rw [fix_X F0 hfix _ hy]
    exact hy)

theorem indQ_mk (c : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) (x : perpS (VS D) F0.X) :
    indQ F0 c hc hfix (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨c x, perp_maps F0 hc hfix _ x.2⟩ := by
  rfl

theorem indQ_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (c : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) (hg : Formalism.HermitianLatticesTheory.gmap c Λ = Λ) :
    indQ F0 c hc hfix ∈ autLz D F0 Λ := by
  refine ⟨c, ⟨hc, fun j => ?_, ?_⟩, hg, fun x hx => indQ_mk F0 c hc hfix x⟩
  · have hfixX : ∀ y ∈ F0.Xa j, c y = y := fun y hy => fix_X F0 hfix y (Xa_le_X F0 j hy)
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      show c z ∈ F0.Xa j
      rw [hfixX z hz]; exact hz
    · intro hy
      exact ⟨y, hy, hfixX y hy⟩
  · have h := hfix (Fin.last D.R.rS)
    simpa [FlagG.fvec] using h

theorem sub_mem_of_indQ {c c' : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) (hc' : c' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hfix' : ∀ a, c' (F0.fvec a) = F0.fvec a) (h : indQ F0 c hc hfix = indQ F0 c' hc' hfix') :
    ∀ y ∈ perpS (VS D) F0.X, c y - c' y ∈ F0.X := by
  intro y hy
  have h1 := congrArg (fun f => f (Submodule.Quotient.mk (⟨y, hy⟩ : perpS (VS D) F0.X))) h
  simp only [indQ_mk] at h1
  rw [Submodule.Quotient.eq] at h1
  simpa using h1

theorem nlam_of_sub {Λ : Submodule (𝓞 D.host.E) (VS D).V} {c c' : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hA : IsAutLam (VS D) Λ c) (hA' : IsAutLam (VS D) Λ c') (hfix : ∀ a, c (F0.fvec a) = F0.fvec a)
    (hfix' : ∀ a, c' (F0.fvec a) = F0.fvec a) (hq : ∀ y ∈ perpS (VS D) F0.X, c y - c' y ∈ F0.X) :
    c⁻¹ * c' ∈ NLam Λ (lf D F0) := by
  obtain ⟨hci, hcg⟩ := hA
  obtain ⟨hci', hcg'⟩ := hA'
  have hX : ∀ x ∈ F0.X, c x = x := fix_X F0 hfix
  have hX' : ∀ x ∈ F0.X, c' x = x := fix_X F0 hfix'
  have hXinv : ∀ x ∈ F0.X, c⁻¹ x = x := fun x hx => by
    show c.symm x = x
    rw [LinearEquiv.symm_apply_eq, hX x hx]
  have hn : ∀ x ∈ F0.X, (c⁻¹ * c') x = x := fun x hx => by
    show c⁻¹ (c' x) = x
    rw [hX' x hx, hXinv x hx]
  refine ⟨⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hci) hci', ?_⟩, fun j x hx => ?_, fun x hx => ?_⟩
  · have hinv : Formalism.HermitianLatticesTheory.gmap c⁻¹ Λ = Λ := by
      conv_lhs => rw [← hcg]
      rw [← gmap_mul_sat, inv_mul_cancel]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [gmap_mul_sat, hcg', hinv]
  · have hxX : x ∈ F0.X := Xa_le_X F0 (j + 1) hx
    rw [hn x hxX, sub_self]
    exact Submodule.zero_mem _
  · have hxp : x ∈ perpS (VS D) F0.X := by
      intro z hz
      have := (Submodule.mem_iInf _).1 hx z
      exact (Submodule.mem_iInf _).1 this hz
    have hd := hq x hxp
    have e1 : (c⁻¹ * c') x - x = c⁻¹ (c' x - c x) := by
      show c⁻¹ (c' x) - x = c⁻¹ (c' x - c x)
      rw [map_sub]
      congr 1
      show x = c.symm (c x)
      rw [LinearEquiv.symm_apply_apply]
    rw [e1]
    have hmem : c' x - c x ∈ F0.X := by
      have := F0.X.neg_mem hd
      simpa using this
    rw [hXinv _ hmem]
    exact hmem

end Flag

section Fib

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem nlam_congr {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V} (h : Λ₁ = Λ₂) {T : D.host.E}
    {F : LFlag (VS D) D.R.rS T} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ₁ F) : n ∈ NLam Λ₂ F := h ▸ hn

theorem gmap_congr {Λ₁ Λ₂ Λ₃ : Submodule (𝓞 D.host.E) (VS D).V} {c : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (h : Formalism.HermitianLatticesTheory.gmap c Λ₁ = Λ₃) (e : Λ₁ = Λ₂) : Formalism.HermitianLatticesTheory.gmap c Λ₂ = Λ₃ := e ▸ h

theorem fib_c {s₀ s : TT Y u u'} (h : s₀.toTerm = s.toTerm) :
    ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V, c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap c s₀.lam' = s₀.lam' ∧
      (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
      ∃ n ∈ NLam s₀.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s₀.lam' (lf D (X.Fu u')), s.lin = n * s₀.lin * ν * c := by
  obtain ⟨-, n, hn, ν, hν, c, hc, hg, hfix, he⟩ := fib_dec h
  exact ⟨c, hc, gmap_congr hg (lam'_eq h).symm, hfix, n, hn, ν, hν, he⟩

theorem eq_of_dec {s₀ s s' : TT Y u u'} (h : s₀.toTerm = s.toTerm) (h' : s₀.toTerm = s'.toTerm)
    {n n' ν ν' c c' : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hn : n ∈ NLam s₀.lam (lf D (X.Fu u))) (hn' : n' ∈ NLam s₀.lam (lf D (X.Fu u)))
    (hν : ν ∈ NLam s₀.lam' (lf D (X.Fu u'))) (hν' : ν' ∈ NLam s₀.lam' (lf D (X.Fu u')))
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hc' : c' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hg : Formalism.HermitianLatticesTheory.gmap c s₀.lam' = s₀.lam') (hg' : Formalism.HermitianLatticesTheory.gmap c' s₀.lam' = s₀.lam')
    (hfix : ∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) (hfix' : ∀ a, c' ((X.Fu u').fvec a) = (X.Fu u').fvec a)
    (he : s.lin = n * s₀.lin * ν * c) (he' : s'.lin = n' * s₀.lin * ν' * c')
    (hq : ∀ y ∈ perpS (VS D) (X.Fu u').X, c y - c' y ∈ (X.Fu u').X) : s = s' := by
  have hl : s₀.lam = s.lam := (fib_dec h).1
  have hl2 : s₀.lam = s'.lam := (fib_dec h').1
  have hm : s₀.lam' = s.lam' := lam'_eq h
  have hm2 : s₀.lam' = s'.lam' := lam'_eq h'
  have hA : IsAutLam (VS D) s₀.lam' c := ⟨hc, hg⟩
  have hA' : IsAutLam (VS D) s₀.lam' c' := ⟨hc', hg'⟩
  have hb := nlam_of_sub (X.Fu u') hA hA' hfix hfix' hq
  have hνν : c⁻¹ * (ν⁻¹ * ν') * c⁻¹⁻¹ ∈ NLam s₀.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.nlam_conj (Formalism.L2.SG.Pf.isAutLam_inv hA) (fun a => (inv_fix (X.Fu u') hfix a).symm)
      (Formalism.L2.SG.Pf.nlamPf_mul (Formalism.L2.SG.Pf.nlamPf_inv hν) hν')
  rw [inv_inv] at hνν
  refine gterm_eq (hl.symm.trans hl2) (hm.symm.trans hm2) ⟨n' * n⁻¹,
    nlam_congr hl (Formalism.L2.SG.Pf.nlamPf_mul hn' (Formalism.L2.SG.Pf.nlamPf_inv hn)),
    (c⁻¹ * (ν⁻¹ * ν') * c) * (c⁻¹ * c'), nlam_congr hm (Formalism.L2.SG.Pf.nlamPf_mul hνν hb), ?_⟩
  rw [he, he']
  group

theorem card_le {t : RT Y u u'} (S0 : Finset (TT Y u u')) (hS0 : ∀ s ∈ S0, s.toTerm = t) {s₀ : TT Y u u'}
    (h₀ : s₀.toTerm = t) [Finite (autLz D (X.Fu u') s₀.lam')] :
    S0.card ≤ Nat.card (autLz D (X.Fu u') s₀.lam') := by
  have hex : ∀ s : S0, ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V, c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      Formalism.HermitianLatticesTheory.gmap c s₀.lam' = s₀.lam' ∧ (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
      ∃ n ∈ NLam s₀.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s₀.lam' (lf D (X.Fu u')),
        (s : TT Y u u').lin = n * s₀.lin * ν * c :=
    fun s => fib_c (h₀.trans (hS0 s s.2).symm)
  let cf : S0 → (VS D).V ≃ₗ[D.host.E] (VS D).V := fun s => (hex s).choose
  have hcf : ∀ s, _ := fun s => (hex s).choose_spec
  let f : S0 → autLz D (X.Fu u') s₀.lam' := fun s =>
    ⟨indQ (X.Fu u') (cf s) (hcf s).1 (hcf s).2.2.1, indQ_mem (X.Fu u') _ _ _ (hcf s).2.1⟩
  have hf : Function.Injective f := by
    intro s s' hss
    have hq := sub_mem_of_indQ (X.Fu u') (hcf s).1 (hcf s).2.2.1 (hcf s').1 (hcf s').2.2.1
      (congrArg Subtype.val hss)
    obtain ⟨n, hn, ν, hν, he⟩ := (hcf s).2.2.2
    obtain ⟨n', hn', ν', hν', he'⟩ := (hcf s').2.2.2
    exact Subtype.ext (eq_of_dec (h₀.trans (hS0 s s.2).symm) (h₀.trans (hS0 s' s'.2).symm) hn hn' hν hν'
      (hcf s).1 (hcf s').1 (hcf s).2.1 (hcf s').2.1 (hcf s).2.2.1 (hcf s').2.2.1 he he' hq)
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_eq_fintype_card] using this

end Fib

section Count

variable {D : D7} {X : HidaSetting D}

variable (Y) in

def RowFree (Y : Full X) : Prop :=
  ∀ (u u' : D.what₂.Word) (s s' : TT Y u u'), s.toTerm = s'.toTerm →
    Formalism.L2.SG.LoopTieOf.rowL (Y := Y) s = Formalism.L2.SG.LoopTieOf.rowL (Y := Y) s' → s = s'

theorem fibreCount_of {Y : Full X} (hR : RowFree Y) : Formalism.L2.SG.LoopTieOf.FibreCount Y := by
  intro u u' t₁ t₂ S hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨x₀, hx₀⟩
  · simp [h0]
  have hlam : ∀ x ∈ S, x.1.lam' = x₀.1.lam' := fun x hx => (lam'_eq ((hS x hx).1.trans (hS x₀ hx₀).1.symm))
  rw [Finset.sum_congr rfl (fun x hx => by rw [hlam x hx]), Finset.sum_const, nsmul_eq_mul]
  unfold wRow
  by_cases hfin : Finite (autLz D (X.Fu u') x₀.1.lam')
  · have hinj : Set.InjOn Prod.fst (S : Set (TT Y u u' × TT Y u u')) := by
      intro x hx y hy hxy
      have h2 : x.2 = y.2 := hR u u' x.2 y.2 ((hS x hx).2.1.trans (hS y hy).2.1.symm)
        (((hS x hx).2.2.symm.trans (congrArg _ hxy)).trans (hS y hy).2.2)
      exact Prod.ext hxy h2
    have hcard : S.card = (S.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    have hle := card_le (S.image Prod.fst) (fun s hs => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hs
        exact (hS x hx).1) (hS x₀ hx₀).1
    rw [← hcard] at hle
    rcases Nat.eq_zero_or_pos (Nat.card (autLz D (X.Fu u') x₀.1.lam')) with hz | hp
    · simp [hz]
    · rw [mul_inv_le_iff₀ (by exact_mod_cast hp), one_mul]
      exact_mod_cast hle
  · have : Infinite (autLz D (X.Fu u') x₀.1.lam') := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite]
    simp

end Count

end Formalism.L2.SG.Pf.FibreCounting
