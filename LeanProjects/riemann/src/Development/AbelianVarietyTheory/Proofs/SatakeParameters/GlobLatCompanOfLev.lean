import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClsCrdEqGlob
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatK
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevStab

section HatS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem lev_mulVec_mem (S : StepLevel F E σ J T f bad) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ S.U)
    (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb) :
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb := by
  refine Formalism.L2.Geo.Def.PN.latS_of_loc S.Lb S.Lb_span _ fun v => ?_
  have h1 := Formalism.L2.Geo.Def.PN.prV_latS S.Lb v hz
  have h2 : bc (prV (E := E) v) g ∈ levelVL σ J v S.Lb := S.Uloc_lev v (((S.U_eq g).1 hg).2 v)
  have h3 := (h2.2 _).1 h1
  have e : (fun i => prV (E := E) v (((g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) i)) =
      ((bc (prV (E := E) v) g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
        fun i => prV (E := E) v (z i) := by
    funext i
    exact RingHom.map_mulVec (prV (E := E) v) (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) z i
  rw [e]
  exact h3

theorem hatStab_lev (S : StepLevel F E σ J T f bad) (κ : S.U) : HatStab S.Lb κ.1 := by
  intro z
  constructor
  · intro hz
    have := lev_mulVec_mem S κ.1 κ.2 _ hz
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  · intro hz
    exact lev_mulVec_mem S κ.1⁻¹ (S.U.inv_mem κ.2) z hz

end HatS

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

local notation "ιA" => Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem incl_int_mem (x : 𝓞 E) : ιA (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E :=
  Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E x, x, rfl⟩, rfl⟩)

theorem ratA_mulVec (γ : GL (Fin N) E) (v : Fin N → E) :
    ((ratA F γ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun l => ιA (v l)) = fun l => ιA (((γ : Matrix (Fin N) (Fin N) E) *ᵥ v) l) := by
  funext l
  exact (RingHom.map_mulVec ιA (γ : Matrix (Fin N) (Fin N) E) v l).symm

theorem exists_den (Q : HeightOneSpectrum (𝓞 E)) (B : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) (hΛ : Λ.FG)
    (hB : mvL B (stdAt E N Q) = Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal Λ) :
    ∃ t ∈ Q.asIdeal.primeCompl, ∀ x ∈ Λ, t • x ∈ mvL B (stdLat E N) := by
  classical
  obtain ⟨S, rfl⟩ := hΛ
  have h1 : ∀ y ∈ S, ∃ s ∈ Q.asIdeal.primeCompl, s • y ∈ mvL B (stdLat E N) := by
    intro y hy
    have hy' : y ∈ mvL B (stdAt E N Q) := by
      rw [hB]
      exact ⟨1, Q.asIdeal.primeCompl.one_mem, by simpa using Submodule.subset_span hy⟩
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy'
    obtain ⟨s, hs, hsu⟩ := hu
    exact ⟨s, hs, Submodule.mem_map.2 ⟨s • u, hsu, by simp⟩⟩
  choose! s hs hsS using h1
  refine ⟨∏ y ∈ S, s y, Finset.prod_induction _ (fun z => z ∈ Q.asIdeal.primeCompl)
    (fun _ _ ha hb => Q.asIdeal.primeCompl.mul_mem ha hb) Q.asIdeal.primeCompl.one_mem hs, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.mul_prod_erase S s hy, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hsS y hy)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ h => rw [smul_comm]; exact Submodule.smul_mem _ _ h

end Gen

section Gen2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

local notation "ιA" => Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem coord_int (B : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) (t : 𝓞 E)
    (ht : ∀ x ∈ Λ, t • x ∈ mvL B (stdLat E N)) (z : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) (k : Fin N) :
    ιA (algebraMap (𝓞 E) E t) * ((((ratA F B)⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) k ∈ Formalism.L2.Herm.intAf F E := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    obtain ⟨u, hu, hux⟩ := Submodule.mem_map.1 (ht x hx)
    have hux' : (B : Matrix (Fin N) (Fin N) E) *ᵥ u = t • x := hux
    rw [← map_inv, GlobalTheory.LevStab.ratA_mulVec]
    have e : ιA (algebraMap (𝓞 E) E t) * ιA ((((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) k) =
        ιA ((((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ (t • x)) k) := by
      rw [← map_mul, Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
    rw [e, ← hux', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (Submodule.mem_pi.1 hu k (Set.mem_univ k))
    rw [← hr]
    exact GlobalTheory.LevStab.incl_int_mem r
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, Pi.add_apply, mul_add]; exact add_mem hx hy
  | smul c x _ h =>
    rw [Subring.smul_def, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
    exact mul_mem c.2 h

theorem int_conj (Q : HeightOneSpectrum (𝓞 E)) (B : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) (hΛ : Λ.FG)
    (hB : mvL B (stdAt E N Q) = Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal Λ) (g : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hg : ∀ x ∈ Λ, (g : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ (fun l => ιA (x l)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ) (i j : Fin N) :
    ∃ s ∈ Q.asIdeal.primeCompl, ιA (algebraMap (𝓞 E) E s) *
      (((ratA F B)⁻¹ * g * ratA F B : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j ∈ Formalism.L2.Herm.intAf F E := by
  classical
  obtain ⟨t, ht, hΛt⟩ := GlobalTheory.LevStab.exists_den Q B Λ hΛ hB
  have hstd : (Pi.single j 1 : Fin N → E) ∈ stdLat E N := by
    refine Submodule.mem_pi.2 fun l _ => ?_
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  have hej : (B : Matrix (Fin N) (Fin N) E) *ᵥ Pi.single j 1 ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal Λ := by
    rw [← hB]
    exact Submodule.mem_map.2 ⟨Pi.single j 1, ⟨1, Q.asIdeal.primeCompl.one_mem, by simpa using hstd⟩, rfl⟩
  obtain ⟨s, hs, hsΛ⟩ := hej
  have h1 := GlobalTheory.LevStab.coord_int B Λ t hΛt _ (hg _ hsΛ) i
  refine ⟨t * s, Q.asIdeal.primeCompl.mul_mem ht hs, ?_⟩
  have e1 : (fun l => ιA ((s • ((B : Matrix (Fin N) (Fin N) E) *ᵥ (Pi.single j (1 : E) : Fin N → E))) l)) =
      ιA (algebraMap (𝓞 E) E s) • (((ratA F B : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ fun l => ιA ((Pi.single j (1 : E) : Fin N → E) l)) := by
    rw [GlobalTheory.LevStab.ratA_mulVec]
    funext l
    rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, smul_eq_mul]
  have e2 : (fun l => ιA ((Pi.single j (1 : E) : Fin N → E) l)) = (Pi.single j 1 : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) := by
    funext l
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [e1, e2, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Pi.smul_apply, smul_eq_mul,
    ← mul_assoc, ← map_mul, Matrix.mulVec_single_one] at h1
  simpa only [Units.val_mul, Matrix.mul_assoc, Matrix.col_apply, map_mul] using h1

end Gen2

theorem globLat_compan_of_lev {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) (a : 𝓞 D.host.E) (g) (hg : g ∈ lev.U) :
    Formalism.UG.CS.globLat g (compan (sp := D.sp) (gramN D i hi) a lev.Lb) = compan (sp := D.sp) (gramN D i hi) a lev.Lb := by
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have hU : g ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((lev.U_eq g).1 hg).1
  have hL : Formalism.UG.CS.globLat g lev.Lb = lev.Lb := by
    have h1 := latAd_stab 1 g lev.Lb (GlobalTheory.LevStab.hatStab_lev lev ⟨g, hg⟩)
    rw [one_mul, GlobalTheory.SDCompan.latAd_eq, GlobalTheory.SDCompan.latAd_eq] at h1
    rw [h1]
    exact Formalism.UG.P.global_lattice_one_holds _ _ _ _ lev.Lb_fin lev.Lb_span
  by_cases ha : a = 0
  · subst ha
    rw [GlobalTheory.SDCompan.compan_zero (sp := D.sp)]
    exact hL
  · have := Formalism.L2.GlobalTheoryTheory.Comp.glob_companion (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.Br.isLat_dlN D i hi) hLb ha g hU
    rw [hL] at this
    rw [GlobalTheory.SDCompan.compan_eq (sp := D.sp)]
    exact this

theorem lev_stab_cong : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) (a : 𝓞 D.host.E) (κ : lev.U)
    (B : GL (Fin (D.R.N i)) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)),
    mvL B (stdAt D.host.E (D.R.N i) Q) = Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (compan (sp := D.sp) (gramN D i hi) a lev.Lb) →
    CongAt (F := D.host.F) Q 0 ((ratA D.host.F B)⁻¹ * κ.1 * ratA D.host.F B) ∧
      CongAt (F := D.host.F) Q 0 ((ratA D.host.F B)⁻¹ * κ.1 * ratA D.host.F B)⁻¹ := by
  intro D i hi T bad lev a κ B Q hB
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have hfix : ∀ g ∈ lev.U, Formalism.UG.CS.globLat g (compan (sp := D.sp) (gramN D i hi) a lev.Lb) =
      compan (sp := D.sp) (gramN D i hi) a lev.Lb := fun g hg => GlobalTheory.LevStab.globLat_compan_of_lev i hi lev a g hg
  have hmem : ∀ g ∈ lev.U, ∀ x ∈ compan (sp := D.sp) (gramN D i hi) a lev.Lb,
      (Units.val g) *ᵥ
        (fun l => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x l)) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (compan (sp := D.sp) (gramN D i hi) a lev.Lb) := by
    intro g hg x hx
    rw [← hfix g⁻¹ (inv_mem hg)] at hx
    have hx' : (Units.val (g⁻¹)⁻¹) *ᵥ
        (fun l => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x l)) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (compan (sp := D.sp) (gramN D i hi) a lev.Lb) := hx
    rwa [inv_inv] at hx'
  have hfg : (compan (sp := D.sp) (gramN D i hi) a lev.Lb).FG := by
    by_cases ha : a = 0
    · subst ha
      rw [GlobalTheory.SDCompan.compan_zero (sp := D.sp)]
      exact Module.Finite.iff_fg.1 lev.Lb_fin
    · rw [GlobalTheory.SDCompan.compan_eq (sp := D.sp)]
      exact Module.Finite.iff_fg.1 (Formalism.L2.GlobalTheoryTheory.Comp.isLat_sup hLb
        (Formalism.L2.GlobalTheoryTheory.Comp.isLat_smul (Formalism.L2.GlobalTheoryTheory.Br.isLat_dlN D i hi _ hLb) ha)).1
  have hcong : ∀ g ∈ lev.U, CongAt (F := D.host.F) Q 0 ((ratA D.host.F B)⁻¹ * g * ratA D.host.F B) := by
    intro g hg c d
    obtain ⟨s, hs, h⟩ := GlobalTheory.LevStab.int_conj (F := D.host.F) (E := D.host.E) Q B _ hfg hB g (hmem g hg) c d
    refine ⟨s, hs, ?_⟩
    rw [pow_zero, inv_one, map_one, one_mul, Matrix.sub_apply, mul_sub]
    refine sub_mem h ?_
    rw [Matrix.one_apply]
    split_ifs
    · rw [mul_one]; exact GlobalTheory.LevStab.incl_int_mem s
    · rw [mul_zero]; exact zero_mem _
  refine ⟨hcong κ.1 κ.2, ?_⟩
  have e : ((ratA D.host.F B)⁻¹ * κ.1 * ratA D.host.F B)⁻¹ = (ratA D.host.F B)⁻¹ * κ.1⁻¹ * ratA D.host.F B := by group
  rw [e]
  exact hcong _ (inv_mem κ.2)

end GlobalTheory.LevStab
