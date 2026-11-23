import Formalism.LocalToGlobal.Columns.TiedXp
import Formalism.LocalToGlobal.Columns.CharactersLevelZeroAgree

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hp_basePi_one (E : Type) [Field E] [NumberField E] [StarRing E] : BasePi (∅ : Finset (Pl E)) (1 : 𝓞 E) where
  dvd r := ⟨fun _ => one_dvd r, fun _ P hP => absurd hP (Finset.notMem_empty P)⟩
  cop := isCoprime_one_left

theorem hp_baseLb_empty (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) [NeZero n] :
    baseLb E n (∅ : Finset (Pl E)) = stdLat E n := by
  refine le_antisymm (rll_baseLb_le n ∅) fun x hx => ?_
  rw [rll_baseLb_eq n (hp_basePi_one E), rll_mem_dLat]
  rw [mem_stdLat] at hx
  refine ⟨fun i _ => hx i, ?_⟩
  rw [map_one, inv_one, one_mul]
  exact hx _

structure HCrdP (X : Fields) (n : ℕ) [NeZero n] {cls : Type} (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  n' : ℕ
  hn : n' = n
  J : Matrix (Fin n') (Fin n') X.E
  hJ : J = 1
  l0 : Submodule (𝓞 X.E) (Fin n' → X.E)
  hl0 : l0 = Formalism.L2.Forms.reL hn.symm (baseLb X.E n (∅ : Finset (Pl X.E)))
  lat : cls → Submodule (𝓞 X.E) (Fin n' → X.E)
  hlat : ∀ c, lat c = Formalism.L2.Forms.reL hn.symm (L c)

structure LevPackP {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (gp : Fin 2 → ℕ) (Lb : Submodule (𝓞 E) (Fin n → E)) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F))
  Uloc_lev : ∀ v, Uloc v ≤ levelVL hc.sig J v Lb
  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∉ v.asIdeal) → ((gp 1 : 𝓞 F) ∉ v.asIdeal) → Uloc v = levelVL hc.sig J v Lb
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F),
    (x ∈ levelVL hc.sig J v Lb ∧ ∀ y ∈ Formalism.L2.Herm.locL v Lb, ∃ z ∈ Formalism.L2.Herm.locL v Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) → x ∈ Uloc v
  U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UPts hc.sig J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v
  cls : RecCls hc J Lb U stab lat

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)

def levPackP₁ (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c) :
    LevPackP hc n (1 : Matrix (Fin n) (Fin n) X.E) Pr.g (baseLb X.E n (∅ : Finset (Pl X.E)))
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.N) where
  Uloc := (tieLevP hc σ₀ Λ).Uloc
  Uloc_lev := (tieLevP hc σ₀ Λ).Uloc_lev
  Uloc_hyp := fun v h0 h1 => (tieLevP hc σ₀ Λ).Uloc_hyp v (fun hb => ((th_plUnder_vGs hc hPr v).1 hb).elim h0 h1)
    (fun h => absurd (by rwa [Nat.cast_one] at h) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top))
  Uloc_g := fun i v hv x hx => by
    refine levLoc_of_princ hc n ∅ Pr.vGs Λ.grp v (Pr.g i) ?_ ?_ x hx.1 hx.2
    · rintro ⟨P, hP, _⟩
      exact absurd hP (Finset.notMem_empty P)
    · intro w _ hov
      have : (Pr.g i : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ hv
      rwa [Ideal.mem_comap, map_natCast] at this
  U := (tieLevP hc σ₀ Λ).U
  U_eq := (tieLevP hc σ₀ Λ).U_eq
  cls :=
    { y := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y
      y_bij := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_bij
      y_lat := fun c x => by
        have h := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_lat c x
        rw [xp_L_eq_N] at h
        exact h
      stabI := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI
      stabI_inj := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_inj
      stabI_range := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_range
      stabI_lat := fun c γ x => by
        have h := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_lat c γ x
        rw [xp_L_eq_N] at h
        exact h }

def levPackP (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (H : HCrdP X n fun c => (s c).1.N) :
    LevPackP hc H.n' H.J Pr.g H.l0 (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) H.lat := by
  obtain ⟨n', hn, J, rfl, l0, hl0, lat, hlat⟩ := H
  subst hn
  obtain rfl : l0 = baseLb X.E n' (∅ : Finset (Pl X.E)) := hl0.trans (Formalism.L2.Forms.reL_rfl _)
  obtain rfl : lat = fun c => (s c).1.N := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact levPackP₁ hc hPr σ₀ Λ s hS hs

theorem levelPacking_sameCarrier (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (H : HCrdP X n fun c => (s c).1.N) (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) :
    Formalism.L2.Forms.SameCar H.hn H.l0 (clsPG hc σ₀ Λ s hS hs Q).lev.Lb
      (levPackP hc hPr σ₀ Λ s hS hs H).Uloc (clsPG hc σ₀ Λ s hS hs Q).lev.Uloc
      (levPackP hc hPr σ₀ Λ s hS hs H).U (clsPG hc σ₀ Λ s hS hs Q).lev.U
      (fun c => ((levPackP hc hPr σ₀ Λ s hS hs H).cls.y c).1) (fun c => ((clsPG hc σ₀ Λ s hS hs Q).y c).1)
      (fun c t => ((levPackP hc hPr σ₀ Λ s hS hs H).cls.stabI c t).1)
      (fun c t => ((clsPG hc σ₀ Λ s hS hs Q).stabI c t).1) := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  obtain ⟨n', hn, J, rfl, l0, hl0, lat, hlat⟩ := H
  subst hn
  obtain rfl : l0 = baseLb X.E n' (∅ : Finset (Pl X.E)) := hl0.trans (Formalism.L2.Forms.reL_rfl _)
  obtain rfl : lat = fun c => (s c).1.N := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact th_sameCar_refl _ _ _ _ _

theorem levelPacking_stabilizer (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (H : HCrdP X n fun c => (s c).1.N) (c : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp)
    (t : MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) :
    Formalism.L2.Forms.reGL H.hn X.E ((levPackP hc hPr σ₀ Λ s hS hs H).cls.stabI c t).1 = ((ratEquiv hc n).symm t.1.1).1 := by
  obtain ⟨n', hn, J, rfl, l0, hl0, lat, hlat⟩ := H
  subst hn
  obtain rfl : l0 = baseLb X.E n' (∅ : Finset (Pl X.E)) := hl0.trans (Formalism.L2.Forms.reL_rfl _)
  obtain rfl : lat = fun c => (s c).1.N := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact Formalism.L2.Forms.reGL_rfl _ _

end Gen

section Repack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
  {S : HSpace E} {gp : Fin 2 → ℕ} {Lb : Submodule (𝓞 E) (Fin S.rank → E)} {cls : Type} {stab : cls → Type}
  [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}

def LevPackP.toStep (P : LevPackP hc S.rank S.gram gp Lb stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.StepLevel0 hc S gp Lb where
  Uloc := P.Uloc
  Uloc_lev := P.Uloc_lev
  Uloc_hyp := P.Uloc_hyp
  Uloc_g := P.Uloc_g
  U := P.U
  U_eq := P.U_eq

def LevPackP.toCls (P : LevPackP hc S.rank S.gram gp Lb stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.ClassTie hc S Lb P.toStep.U stab lat where
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := fun c γ => P.cls.stabI_range c γ.1 γ.2

end Repack

end Formalism.L2.Col
