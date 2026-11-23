import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZeroCocycleSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsQuotPartGraded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

set_option maxHeartbeats 1000000 in

theorem FibreSectionLift.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hsq : KH.CechDSqStatement) (hdg : KH.CechDDegStatement) (hR : ReductionComplex.Statement)
    (hZ : ZeroCocycleSection.Statement) (hC : SecCochReduce.Statement) : FibreSectionLift.Statement := by
  intro K _ _ ι _ _ Ω _ y D p a hV hp hH1
  have hH1' : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) := hH1
  show ∀ z ∈ KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 0,
    ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y (ZMod p) s a = z
  intro z hz'

  let instC : ∀ n : ℕ, Module ℤ (KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n) := fun n =>
    (fun {A : Type} {_ : AddCommMonoid A} {i : Module ℤ A} (_ : Submodule ℤ A) => i)
      (KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n)
  let instZ : Module ℤ (KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := Submodule.module _
  let instCp : ∀ n : ℕ, Module (ZMod p) (KH.CechC (ZMod p) ι (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) n) :=
    fun n => (fun {A : Type} {_ : AddCommMonoid A} {i : Module (ZMod p) A} (_ : Submodule (ZMod p) A) => i)
      (KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n)
  let instZp : Module (ZMod p) (KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) :=
    Submodule.module _
  let instH : Module ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) :=
    Submodule.Quotient.module _
  obtain ⟨hd, hrd, hon, hker₀, hnzd₀, hkill₀⟩ := hR K ι Ω y D p a hV hp

  have hker : ∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w = 0 →
        ∃ w' ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, w = (p : ℤ) • w' := by
    intro n w hw h0
    obtain ⟨w', h1, h2⟩ := hker₀ n w hw h0
    exact ⟨w', h1, by convert h2 using 2⟩
  have hnzd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      (p : ℤ) • w = 0 → w = 0 := fun n w h => hnzd₀ n w (by convert h using 2)
  have hkill : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p n ((p : ℤ) • w) = 0 := fun n w => by convert hkill₀ n w using 3
  have hgr : KH.IsMGraded ℤ ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) :=
    hG ℤ K ι _ (by rw [FibreReduction.idealOver_int]; exact hV.2.1.2.1)
  have hfin : Module.Finite ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := by
    exact (hS ℤ K ι _ _ inferInstance inferInstance hgr).1 a 1
  have dd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ (n + 1) (KH.cechD ℤ ι _ n w) = 0 := fun n w =>
    LinearMap.congr_fun (hsq ℤ K ι _ n) w
  have dsmul : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ n ((p : ℤ) • w) = (p : ℤ) • KH.cechD ℤ ι _ n w := fun n w =>
    map_zsmul (KH.cechD ℤ ι _ n).toAddMonoidHom (p : ℤ) w
  have memZ : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n → KH.cechD ℤ ι _ n w = 0 →
        w ∈ KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n := fun n w hC hD =>
    Submodule.mem_inf.mpr ⟨hC, by rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]; exact hD⟩

  let f : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 →ₗ[ℤ]
      KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 := LinearMap.lsmul ℤ _ (p : ℤ)
  have hq : ∀ x : KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1,
      f (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((p : ℤ) • x) := fun x => by
    rw [LinearMap.lsmul_apply, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, map_zsmul]
    exact int_smul_eq_zsmul instH (p : ℤ) _
  have hsurj : Function.Surjective f := by
    intro h
    induction h using Submodule.Quotient.induction_on with
    | H x =>
    have hx := Submodule.mem_inf.mp x.2
    have hxd : KH.cechD ℤ ι _ 1 x.1 = 0 := by
      have := hx.2
      rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
    have hrx : FibreReduction.redCoch y p 1 x.1 ∈
        KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1 :=
      Submodule.mem_inf.mpr ⟨hrd 1 _ hx.1, by
        rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, ← hd, hxd, map_zero]⟩
    have h0' : (Submodule.Quotient.mk ⟨_, hrx⟩ :
        KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) = 0 := Subsingleton.elim _ _
    have h0 := (Submodule.Quotient.mk_eq_zero _).mp h0'
    obtain ⟨u, hu, hdu⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp h0)
    obtain ⟨u', hu', hru'⟩ := hon 0 u hu
    have hdu' := hdg ℤ K ι _ _ a 0 u' hu'
    obtain ⟨x', hx'C, hx'eq⟩ := hker 1 (x.1 - KH.cechD ℤ ι _ 0 u') (sub_mem hx.1 hdu') (by
      rw [map_sub, hd, hru']
      exact sub_eq_zero.mpr hdu.symm)
    have hx'Z := memZ 1 x' hx'C (hnzd 2 _ (by rw [← dsmul, ← hx'eq, map_sub, hxd, dd, sub_self]))
    refine ⟨Submodule.Quotient.mk ⟨x', hx'Z⟩, ?_⟩
    rw [hq, Submodule.Quotient.eq, Submodule.mem_comap, map_sub, map_zsmul]
    refine Submodule.mem_map.mpr ⟨-u', neg_mem hu', ?_⟩
    rw [LinearMap.restrictScalars_apply, map_neg, Submodule.subtype_apply, Submodule.subtype_apply]
    show _ = (p : ℤ) • x' - x.1
    rw [← hx'eq]
    abel
  have hinj : Function.Injective f := OrzechProperty.injective_of_surjective_endomorphism f hsurj

  obtain ⟨w, hwC, hrw⟩ := hon 0 z (Submodule.mem_inf.mp hz').1
  have hzd : KH.cechD (ZMod p) ι _ 0 z = 0 := by
    have := (Submodule.mem_inf.mp hz').2
    rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
  obtain ⟨w', hw'C, hw'eq⟩ := hker 1 _ (hdg ℤ K ι _ _ a 0 w hwC) (by rw [hd, hrw, hzd])
  have hw'Z := memZ 1 w' hw'C (hnzd 2 _ (by rw [← dsmul, ← hw'eq, dd]))
  have hcls : (Submodule.Quotient.mk ⟨w', hw'Z⟩ : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) = 0 := by
    apply hinj
    rw [map_zero, hq, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_zsmul, Submodule.subtype_apply]
    exact Submodule.mem_map.mpr ⟨w, hwC, hw'eq⟩
  obtain ⟨v, hvC, hdv⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp hcls))
  have hv0 := memZ 0 (w - (p : ℤ) • v) (sub_mem hwC (zsmul_mem hvC _)) (by
    rw [map_sub, dsmul]
    rw [LinearMap.restrictScalars_apply] at hdv
    rw [hdv]
    exact sub_eq_zero.mpr hw'eq)
  obtain ⟨s, hs, hsv⟩ := hZ K ι Ω y a _ hv0
  refine ⟨s, hs, ?_⟩
  rw [← hC K ι Ω y p a s hs, hsv, map_sub, hkill, sub_zero, hrw]

end GroundTheory.Heights₂.Heights.HilbertSamuel
