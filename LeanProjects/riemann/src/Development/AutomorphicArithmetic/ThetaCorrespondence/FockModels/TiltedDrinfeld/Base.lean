import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.BaseThetaVanishing.BaseThZero
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.BaseAinfPlus
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.BasedP
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.BaseFixed

noncomputable section

namespace period_ring_base

theorem base : PeriodRingBase := fun l _ =>
  { dom := base_dom l
    ι_inj := base_ι_inj l
    σ_one := base_σ_one l
    σ_mul := base_σ_mul l
    σD_one := base_σD_one l
    σD_mul := base_σD_mul l
    σC_one := base_σC_one l
    σC_mul := base_σC_mul l
    φ_σ := base_φ_σ l
    ι_σ := base_ι_σ l
    φ_q := base_φ_q l
    σ_q := base_σ_q l
    ι_q := base_ι_q l
    ι_t := period_image_eq l
    t_unit := base_t_unit l
    frobenius_period := frobenius_period_holds l
    galois_t_transform := galois_period_cyclotomic l
    σ_u := base_σ_u l
    κ_mul := base_κ_mul l
    κ_cont := base_κ_cont l
    χ_cont := base_χ_cont l
    ι_Bst := base_ι_Bst l
    u_Bst := base_u_Bst l
    plus_σ := base_plus_σ l
    th_σ := base_th_σ l
    th_add := base_th_add l
    th_mul := base_th_mul l
    th_q := base_th_q l
    th_zero := base_th_zero l
    t_plus := base_t_plus l
    val := base_val l
    orbit := base_orbit l
    fs_ker := base_fs_ker l
    fs_surj := base_fs_surj l
    ainf_φ := base_ainf_φ l
    ainf_σ := base_ainf_σ l
    ainf_plus := base_ainf_plus l
    ainf_eig := base_ainf_eig l
    fixed := base_fixed' l
    no_kummer := base_no_kummer l }

end period_ring_base
