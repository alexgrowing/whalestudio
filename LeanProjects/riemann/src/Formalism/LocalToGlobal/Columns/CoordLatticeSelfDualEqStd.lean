import Formalism.LocalToGlobal.Columns.LocalLevelIsKOneEverywhere
import Formalism.LocalToGlobal.Columns.TiedHK
import Formalism.LocalToGlobal.Columns.ThBaseCompanion

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

include hX hPr in

theorem localLevelIsKOneAtT_holds : LocalLevelIsKOneAtT hc u Λ := fun v hv x =>
  localLevel_iff_kOne hc n Pr.vGs Λ.grp v (basePi_of_ok hX hPr u) (rls_T_notUnder hPr u v hv) x

variable (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem th_reL_std {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : a = b) :
    Formalism.L2.Forms.reL h (stdLat E a) = stdLat E b := by
  subst h
  exact Formalism.L2.Forms.reL_rfl _

theorem levPack_base (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) (pb : 𝓞 X.E)
    (hpb : algebraMap (𝓞 X.E) X.E pb = star (algebraMap (𝓞 X.E) X.E (Pr.piT u))) :
    (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 X.E)
      (dualSet (hc.sig : X.E →+* X.E) H.J (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb) = stdLat X.E H.n' := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact th_base_companion hc _ (basePi_of_ok hX hPr u) pb hpb

end Gen

theorem th_map_span_std {E V : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] {r r' : ℕ} (e : V ≃ₗ[E] (Fin r → E)) (b : Fin r' → V) (σ : Fin r' ≃ Fin r)
    (hb : ∀ a, e (b a) = Pi.single (σ a) (1 : E)) :
    (Submodule.span (𝓞 E) (Set.range b)).map ((e : V →ₗ[E] (Fin r → E)).restrictScalars (𝓞 E)) = stdLat E r := by
  rw [Submodule.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    show e (b a) ∈ _
    rw [hb]
    simpa using single_mem_stdLat (E := E) (σ a) 1
  · intro x hx
    rw [mem_stdLat] at hx
    choose t ht using hx
    have hsum : x = ∑ j, t j • e (b (σ.symm j)) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [hb, Equiv.apply_symm_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one, ht]
      · intro j _ hj
        rw [hb, Equiv.apply_symm_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

variable {d : ColDat}

theorem localLevelIsKOne_everywhere (d : ColDat) : LocalLevelIsKOneEverywhere d := fun u i => localLevelIsKOneAtT_holds d.sp.cm d.hX d.hPr u (d.lev i)

theorem coordLattice_selfDual_eq_std (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) :
    Formalism.L2.Herm.crdLat (d.sp.X i) (d.sp.X i).L0 = stdLat d.X.E (d.sp.X i).rank := by
  unfold Formalism.L2.Herm.crdLat
  rw [hS.selfDual_span_frame_X i hi]
  refine th_map_span_std (Formalism.L2.Herm.crd (d.sp.X i)) _ (Equiv.refl _) fun a => ?_
  funext j
  show (d.sp.X i).frame.equivFun ((d.sp.X i).frame a) j = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext eq_comm

theorem coordLattice_selfDual_zero (hS : SpStd d.toColBase) : d.sp.crdLat0 (d.sp.X 0).L0 = stdLat d.X.E d.R.k := by
  unfold Spaces.crdLat0
  rw [hS.selfDual_span_frame_X 0 (Nat.zero_le _)]
  refine th_map_span_std d.sp.crd0 _ (finCongr d.sp.rank0) fun a => ?_
  funext j
  show (d.sp.X 0).frame.equivFun ((d.sp.X 0).frame a) ((finCongr d.sp.rank0).symm j) = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by rw [h, Equiv.symm_apply_apply]⟩

end Formalism.L2.Col
